#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/force_lhs.h"
#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_key_match.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

// §5.10 and §5.11: the replication an assignment pattern consists of,
// `'{n{...}}`, or null for a pattern of any other form.
const Expr* PatternReplication(const Expr* pattern) {
  if (pattern->elements.size() != 1) return nullptr;
  const Expr* only = pattern->elements[0];
  return only->is_pattern_replication ? only : nullptr;
}

// §5.10 and §5.11: the items a positional pattern supplies -- its elements, or
// a replication's multiplier times the items inside it, the inner braces being
// removed -- or nothing where the multiplier does not fold.
std::optional<int64_t> PositionalItemCount(const Expr* pattern) {
  const Expr* rep = PatternReplication(pattern);
  if (rep == nullptr) return static_cast<int64_t>(pattern->elements.size());
  auto times = ConstEvalInt(rep->repeat_count);
  if (!times) return std::nullopt;
  return *times * static_cast<int64_t>(rep->elements.size());
}

// The number of elements the range [left:right] spans, or nothing where a
// bound does not fold.
static std::optional<int64_t> RangeSize(const Expr* left, const Expr* right) {
  auto left_value = ConstEvalInt(left);
  auto right_value = ConstEvalInt(right);
  if (left_value && right_value)
    return std::abs(*left_value - *right_value) + 1;
  return std::nullopt;
}

std::optional<int64_t> ComputeDimSize(const Expr* dim) {
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon)
    return RangeSize(dim->lhs, dim->rhs);
  return ConstEvalInt(dim);
}

namespace {
// One dimension an array pattern's braces stand for (§10.9.1): the number of
// its elements, or nothing where that does not fold or the dimension has no
// fixed size, and whether it is one of the packed dimensions (§7.4).
struct PatternDim {
  std::optional<int64_t> size;
  bool packed = false;
};
}  // namespace

// §7.4: appends the packed dimensions `dtype` is written
// with, outermost first.
static void AppendPackedDims(const DataType& dtype,
                             std::vector<PatternDim>& dims) {
  if (dtype.packed_dim_left == nullptr) return;
  dims.push_back(
      {RangeSize(dtype.packed_dim_left, dtype.packed_dim_right), true});
  for (const auto& [left, right] : dtype.extra_packed_dims)
    dims.push_back({RangeSize(left, right), true});
}

// §7.4 with §6.18: appends the packed dimensions of an array's element type
// `dtype`, which its braces go on into once the unpacked dimensions are spent:
// those written on the type, then those of each typedef it names in turn. The
// walk stops at a typedef whose name stands for an unpacked aggregate, whose
// unpacked dimensions come before any packed one, and at a name this scope
// does not resolve.
static void AppendElementPackedDims(const ArrayPatternCheck& check,
                                    const DataType& dtype,
                                    std::vector<PatternDim>& dims) {
  AppendPackedDims(dtype, dims);
  std::vector<std::string_view> names;
  FollowTypedefs(dtype, check.typedefs, names);
  for (std::string_view name : names) {
    auto it = check.typedefs.find(name);
    if (it == check.typedefs.end() || check.aggregate_typedefs.contains(name))
      return;
    AppendPackedDims(it->second, dims);
  }
}

// What two array pattern keys are the same key by. §10.9's array keys are
// constant expressions, so what a key names is its value: `3` and `N-1` with N
// of 4 name the element between them once, not twice. A key that does not fold
// here is answered for by how it was written, which still tells apart the two
// halves of a key written the same way twice. Nothing for a key that neither
// folds nor was written as a single name or literal -- there is no ground to
// call two of those the same, and calling them so would report every pair of
// them as a duplicate.
static std::optional<std::string> ArrayPatternKeyIdentity(const Expr* key) {
  auto value = ConstEvalInt(key);
  if (value) return std::to_string(*value);
  if (key->text.empty()) return std::nullopt;
  return std::string(key->text);
}

static void CheckArrayPatternDuplicateIndices(const Expr* init, SourceLoc loc,
                                              const TypedefMap& typedefs,
                                              DiagEngine& diag) {
  std::unordered_set<std::string> seen;
  for (const auto* key : init->pattern_keys) {
    if (key->text == "default" || IsTypeKey(key->text, typedefs)) continue;
    auto identity = ArrayPatternKeyIdentity(key);
    if (!identity) continue;
    if (!seen.insert(*identity).second) {
      diag.Error(
          loc,
          std::format("duplicate index key '{}' in array pattern", *identity),
          Subclause("10.9.1"));
    }
  }
}

// §10.9.1 (printed page 262): a type key that matches no element of an array
// of structures descends into each element and applies to the members of its
// type, so it covers an element whose every member it matches.
static bool TypeKeyCoversElement(std::string_view key, const DataType& elem,
                                 const TypedefMap& typedefs) {
  if (TypeKeyMatchesType(key, elem, typedefs)) return true;
  std::vector<std::string_view> names;
  const DataType* agg = FollowTypedefs(elem, typedefs, names);
  if (agg == nullptr || agg->struct_members.empty()) return false;
  return std::ranges::all_of(agg->struct_members, [&](const StructMember& m) {
    return TypeKeyMatchesMember(key, m, typedefs);
  });
}

static void CheckArrayPatternCoverage(const ArrayPatternCheck& check,
                                      const Expr* pattern,
                                      const DataType& elem_type,
                                      const PatternDim& dim, SourceLoc loc) {
  const TypedefMap& typedefs = check.typedefs;
  if (!dim.size) return;

  bool has_default = false;
  bool has_type_key = false;
  std::unordered_set<std::string> index_keys;
  // Keys with no identity are counted rather than collected. Each one is still
  // a key, and leaving them out would read a pattern whose keys the elaborator
  // cannot fold as covering fewer elements than it was written for.
  int64_t unidentified_keys = 0;
  for (const auto* key : pattern->pattern_keys) {
    if (key->text == "default") {
      has_default = true;
    } else if (IsTypeKey(key->text, typedefs)) {
      // §10.9.1's type key covers each field whose type matches its type, so a
      // key naming a type the element is not declared with covers nothing and
      // cannot exempt the pattern from the count below:
      // `logic [7:0] arr [0:2] = '{int: 8'h05};` names no element by index,
      // carries no default and matches no element by type, which the clause's
      // requirement that one of these rules cover every element forbids and
      // this accepted. The element type is asked rather than a subarray's,
      // because the clause descends into each subarray, applying the same rules
      // and the type and default keys -- a key matching the leaf type covers a
      // multidimensional array at every level, which is what CreateMultiDimLeaf
      // already does. A packed dimension's element is `elem_type` with that
      // dimension and those outside it taken off, a type `elem_type` does not
      // describe, so a type key there is taken to cover it.
      has_type_key = has_type_key || dim.packed ||
                     TypeKeyCoversElement(key->text, elem_type, typedefs);
    } else if (auto identity = ArrayPatternKeyIdentity(key)) {
      index_keys.insert(*identity);
    } else {
      ++unidentified_keys;
    }
  }
  if (has_default || has_type_key) return;
  if (static_cast<int64_t>(index_keys.size()) + unidentified_keys < *dim.size) {
    check.diag.Error(loc, "keyed array pattern does not cover all elements",
                     Subclause("10.9.1"));
  }
}

// §5.10 (printed page 84): whether a declaration's type is an unpacked
// structure, written inline or through a typedef. A packed structure is left
// out on purpose: §7.2.1 has one take an integral value as a whole, so a
// literal per element of an array of packed structures is a value per element
// and not the flat form the clause does not allow.
static bool IsUnpackedStructType(const DataType& dt,
                                 const TypedefMap& typedefs) {
  const DataType* t = &dt;
  if (t->kind == DataTypeKind::kNamed) {
    auto td = typedefs.find(t->type_name);
    if (td == typedefs.end()) return false;
    t = &td->second;
  }
  return t->kind == DataTypeKind::kStruct && !t->is_packed;
}

// §5.10: whether an element of a pattern initializing an array of structures
// is a value that can be no structure, which is what makes the pattern the
// C-like flat form the clause names as not allowed. A literal is one; so is a
// name declared with a built-in integral, real or string type. A nested
// pattern, a name of a structure or of a type this table does not record, a
// call, a select or a member access is not decided against: the flat form is
// told from the legal `'{s1, s2}` of two structure variables only by the type
// of each element, and the declared kinds of names are all this pass carries.
static bool IsElementThatIsNoStruct(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return true;
    case ExprKind::kIdentifier: {
      auto it = var_types.find(e->text);
      if (it == var_types.end()) return false;
      DataTypeKind kind = it->second;
      return (IsIntegralType(kind) && kind != DataTypeKind::kImplicit) ||
             IsRealType(kind) || kind == DataTypeKind::kString;
    }
    default:
      return false;
  }
}

// §5.10: an initialized array of structures nests a pattern per structure
// inside the array's braces. A top-level element that can be no structure
// makes the pattern the flat form, and that is the rule the spelling breaks
// rather than the element count, which the flat form fails only when the
// counts happen to disagree. Whether the pattern was reported.
static bool ReportsFlatStructPattern(const ArrayPatternCheck& check,
                                     const Expr* pattern,
                                     const DataType& elem_type, SourceLoc loc) {
  if (!IsUnpackedStructType(elem_type, check.typedefs)) return false;
  for (const auto* e : pattern->elements) {
    if (IsElementThatIsNoStruct(e, check.var_types)) {
      check.diag.Error(loc,
                       "assignment pattern for an array of structures shall "
                       "nest a pattern per structure",
                       Subclause("5.10"));
      return true;
    }
  }
  return false;
}

// Checks `pattern` against the dimensions `dims`, outermost first, of an array
// of `elem_type`.
static void CheckPatternDims(const ArrayPatternCheck& check,
                             const Expr* pattern, const DataType& elem_type,
                             std::span<const PatternDim> dims, SourceLoc loc) {
  if (pattern->kind != ExprKind::kAssignmentPattern || dims.empty()) return;
  if (!pattern->pattern_keys.empty()) {
    CheckArrayPatternDuplicateIndices(pattern, loc, check.typedefs, check.diag);
    CheckArrayPatternCoverage(check, pattern, elem_type, dims[0], loc);
    return;
  }
  if (ReportsFlatStructPattern(check, pattern, elem_type, loc)) return;
  const std::optional<int64_t> kDimSize = dims[0].size;
  if (!kDimSize) return;
  // §5.11: a replication operates within one dimension, so what it supplies
  // is counted against that dimension as a positional list is.
  auto count = PositionalItemCount(pattern);
  if (count && *count != *kDimSize) {
    check.diag.Error(loc,
                     std::format("assignment pattern has {} elements, but "
                                 "array dimension requires {}",
                                 *count, *kDimSize),
                     Subclause("10.9.1"));
  }
  // §10.9.1 (printed pages 261-262): the braces match the dimensions, each
  // nested pattern holding as many items as the dimension it stands for.
  for (const Expr* e : pattern->elements)
    CheckPatternDims(check, e, elem_type, dims.subspan(1), loc);
}

// Checks `pattern` against the unpacked dimensions `dims` of an array of
// `elem_type` and then against the packed dimensions of `elem_type`.
static void CheckAgainstUnpackedDims(const ArrayPatternCheck& check,
                                     const Expr* pattern,
                                     const DataType& elem_type,
                                     std::vector<PatternDim> dims,
                                     SourceLoc loc) {
  AppendElementPackedDims(check, elem_type, dims);
  CheckPatternDims(check, pattern, elem_type, dims, loc);
}

void ArrayPatternCheck::Check(const Expr* pattern, const DataType& elem_type,
                              const std::vector<Expr*>& dims,
                              SourceLoc loc) const {
  std::vector<PatternDim> pattern_dims;
  pattern_dims.reserve(dims.size());
  for (const Expr* dim : dims) {
    pattern_dims.push_back(
        {dim == nullptr ? std::nullopt : ComputeDimSize(dim), false});
  }
  CheckAgainstUnpackedDims(*this, pattern, elem_type, std::move(pattern_dims),
                           loc);
}

void ArrayPatternCheck::CheckSized(const Expr* pattern,
                                   const DataType& elem_type,
                                   std::span<const uint32_t> unpacked_sizes,
                                   SourceLoc loc) const {
  std::vector<PatternDim> pattern_dims;
  pattern_dims.reserve(unpacked_sizes.size());
  for (uint32_t size : unpacked_sizes) pattern_dims.push_back({size, false});
  CheckAgainstUnpackedDims(*this, pattern, elem_type, std::move(pattern_dims),
                           loc);
}

void Elaborator::ValidateArrayInitPattern(const ModuleItem* item) {
  if (!item->init_expr) return;
  ArrayPatternCheck{typedefs_, aggregate_typedef_names_, var_types_, diag_}
      .Check(item->init_expr, item->data_type, item->unpacked_dims, item->loc);
}

std::string_view ExprIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

// The data object a left-hand side or an operand ultimately names: §23.7 calls
// `a.b[2].c` a dotted name and rules that a member select's first name
// component matches a data object or interface port name, and this returns that
// first component. Each node kind is descended by the field the parser actually
// fills: a select hangs its prefix off `base`, and a member access off `lhs` --
// Parser::MakeMemberAccess and Parser::ParseForeachArrayId both set `lhs` and
// leave `base` null, so following `base` throughout walked off the end of every
// dotted name and answered the empty one, which each caller reads as "nothing
// to check".
//
// Two spellings end the walk rather than being descended:
//
//   A scope resolution wears ExprKind::kMemberAccess too, and §23.7.1 has a
//   name with a package or class scope resolution prefix (::) resolve
//   downwards through that prefix, which names a package or a class rather than
//   a data object. Returning `C` for `C::x = 1` would offer every caller a name
//   from the wrong namespace to match its variables against.
//
//   `this` and `super` parse as an identifier of that text under a member
//   access, and neither is a declared variable, so no caller's set can hold
//   one. The walk stops with the empty name, which is what the callers did with
//   these before and what keeps a write through `this` from being recorded
//   against a variable that happens to be spelled that way.
std::string_view LhsBaseName(const Expr* e) {
  while (e) {
    if (e->kind == ExprKind::kIdentifier)
      return (e->text == "this" || e->text == "super") ? std::string_view{}
                                                       : e->text;
    if (e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution) {
      e = e->lhs;
      continue;
    }
    if (e->kind == ExprKind::kSelect) {
      e = e->base;
      continue;
    }
    break;
  }
  return {};
}

// §6.21 (printed page 134), first sentence: no continuous or procedural
// continuous assignment may write an element of a dynamically sized array
// variable, and `b[2].x` falls under it, because the name is a member while
// the object the write lands in is the element `b[2]`, and writing part of an
// element is writing it. The nonblocking half of the sentence, which §10.4.2
// states for itself, is CheckNbaDynamicElements in nba_dynamic_element.cpp.
static void ReportDynamicLvalueAssign(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag) {
  if (s->kind != StmtKind::kForce && s->kind != StmtKind::kAssign) return;
  // The kind gate rather than the walk is what confines this to a part of a
  // dynamic array: a bare identifier lvalue is a write to the whole object,
  // which the clause permits, and LhsBaseName answers the same name for it as
  // for a select of it.
  if (s->lhs->kind != ExprKind::kSelect &&
      s->lhs->kind != ExprKind::kMemberAccess)
    return;
  if (dyn_names.count(LhsBaseName(s->lhs)) != 0) {
    diag.Error(s->range.start,
               "procedural continuous assignment to element of "
               "dynamic array",
               Subclause("6.21"));
  }
}

void CheckPcontDynamicArrayTarget(
    const Stmt* s, const std::unordered_set<std::string_view>& dyn_names,
    DiagEngine& diag) {
  if (!s) return;
  ReportDynamicLvalueAssign(s, dyn_names, diag);
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckPcontDynamicArrayTarget(sub, dyn_names, diag);
  });
}

static void CollectLhsBaseNames(
    const Expr* e, SourceLoc loc,
    std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!e) return;
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* elem : e->elements) CollectLhsBaseNames(elem, loc, out);
    return;
  }
  auto name = LhsBaseName(e);
  if (!name.empty()) out.emplace(name, loc);
}

// Records the variable each blocking or nonblocking assignment writes, for
// §6.5's rule making it an error for several continuous assignments, or a
// mixture of procedural and continuous ones, to write any term of a variable's
// longest static prefix expansion, and for §10.4's rule that a procedural
// assignment's left-hand side be a variable. Both tests read sets that are
// complete only after every item has been walked, so this only collects;
// Elaborator::ValidateMixedAssignments and
// Elaborator::ValidateProceduralNetAssign report.
//
// The statement position an assignment stands in decides neither rule, so
// every statement of `body` is visited. §23.9 decides what a name reaches, so a
// name the body itself declares -- a formal of `formals`, a block's variable,
// a loop's -- is the body's own and none of the module's, and is not recorded.
void CollectProcTargets(const std::vector<FunctionArg>& formals,
                        const std::vector<Stmt*>& body,
                        std::unordered_map<std::string_view, SourceLoc>& out) {
  BodyDeclScopes scopes(false);
  for (const auto& arg : formals) scopes.DeclareFormal(arg);
  std::unordered_map<std::string_view, SourceLoc> written;
  for (const Stmt* s : body) {
    scopes.Walk(s, [&](const Stmt* st) {
      if (st->kind != StmtKind::kBlockingAssign &&
          st->kind != StmtKind::kNonblockingAssign)
        return;
      written.clear();
      CollectLhsBaseNames(st->lhs, st->range.start, written);
      for (const auto& [name, loc] : written)
        if (scopes.Find(name) == nullptr) out.emplace(name, loc);
    });
  }
}

// Records the variable each force or release statement names, for §10.6.2's
// rule that neither may be applied to a variable assigned by a mixture of
// continuous and procedural assignments. The rule reads sets that are complete
// only after every item has been walked, so the test itself is left to
// Elaborator::ValidateMixedAssignments and this only collects. Uses the same
// CollectLhsBaseNames as CollectProcTargets, which descends a concatenation,
// because §10.6.2 admits a concatenation of those forms as a force target and
// the rule holds of each operand. Recurses through ForEachChildStmt for the
// reason CollectProcTargets above does: where a force or release is written
// decides nothing about the rule.
void CollectForceReleaseTargets(
    const Stmt* s, std::unordered_map<std::string_view, SourceLoc>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kRelease) {
    CollectLhsBaseNames(s->lhs, s->range.start, out);
  }
  ForEachChildStmt(
      s, [&out](const Stmt* sub) { CollectForceReleaseTargets(sub, out); });
}

void CheckInterconnectProcContAssign(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce || s->kind == StmtKind::kRelease ||
      s->kind == StmtKind::kAssign || s->kind == StmtKind::kDeassign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty() && interconnect_names.count(name)) {
      diag.Error(s->range.start,
                 "interconnect net cannot be used in procedural "
                 "continuous assignment",
                 Subclause("6.6.8"));
    }
  }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckInterconnectProcContAssign(sub, interconnect_names, diag);
  });
}

// §6.6.8: an interconnect net is typeless/generic and shall not be used in any
// procedural context, nor in any expression other than a net_lvalue whose nets
// are all interconnect. Procedural-assignment targets are already rejected (by
// the net-target rule and CheckInterconnectProcContAssign); this closes the
// read side by flagging any interconnect net appearing in a procedural
// statement's read expressions — an assignment RHS, an if/case/loop condition,
// a case pattern, a delay, an assertion expression, or a call argument.
void CheckInterconnectProceduralRead(
    const Stmt* s,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  if (!s) return;
  const Expr* reads[] = {s->rhs,      s->condition,          s->for_cond,
                         s->delay,    s->cycle_delay,        s->expr,
                         s->var_init, s->repeat_event_count, s->assert_expr};
  for (const Expr* e : reads) {
    if (ExprUsesInterconnect(e, interconnect_names)) {
      diag.Error(s->range.start,
                 "interconnect net cannot be used in a procedural expression",
                 Subclause("6.6.8"));
      break;
    }
  }
  for (auto& ci : s->case_items)
    for (const auto* p : ci.patterns)
      if (ExprUsesInterconnect(p, interconnect_names)) {
        diag.Error(s->range.start,
                   "interconnect net cannot be used in a procedural expression",
                   Subclause("6.6.8"));
        break;
      }
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckInterconnectProceduralRead(sub, interconnect_names, diag);
  });
}

// §10.6.1: the LHS of an assign statement shall be a singular variable
// reference or a concatenation of variables, and shall not be a bit-select or a
// part-select of a variable. Because the concatenation must be one *of
// variables*, a bit-select or part-select element inside the concatenation is
// equally illegal, so the check descends through concatenations rather than
// only inspecting the top-level lvalue.
static bool ProceduralAssignLhsHasSelect(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kSelect) return true;
  if (e->kind == ExprKind::kConcatenation) {
    for (const auto* elem : e->elements)
      if (ProceduralAssignLhsHasSelect(elem)) return true;
  }
  return false;
}

void CheckProceduralAssignLhs(const Stmt* s, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kAssign && ProceduralAssignLhsHasSelect(s->lhs)) {
    diag.Error(s->range.start,
               "bit-select or part-select in procedural assign LHS",
               Subclause("10.6.1"));
  }
  ForEachChildStmt(
      s, [&diag](const Stmt* sub) { CheckProceduralAssignLhs(sub, diag); });
}

// What the variable target of a force names: a singular variable, which
// §10.6.2 admits; a variable of an unpacked array, structure or union type, or
// a slice or sub-array of one, none of them singular (§6.4); or bits of a
// vector, a bit-select or part-select (§11.5.1), which §10.6.2 bars.
enum class ForceVariableTarget { kSingular, kAggregate, kBits };

// §6.4 with §11.5.2: what `e`, a name or a chain of selects down from one,
// names. The select next to the name addresses the first unpacked dimension
// the variable declares: one address for each, with no range among them,
// selects an element, a variable of the element type; a range among them
// selects a slice, and fewer addresses a sub-array. Addresses past the unpacked
// dimensions select bits of the element. A name the module declares no
// variable of, such as one reached through a member select, has no unpacked
// dimension known here and an element type that is no aggregate.
static ForceVariableTarget ClassifyForceVariableTarget(
    const Expr* e, const ForceLhsNames& names) {
  std::vector<const Expr*> selects;
  for (; e->kind == ExprKind::kSelect; e = e->base)
    selects.insert(selects.begin(), e);
  std::string_view name =
      e->kind == ExprKind::kIdentifier ? e->text : std::string_view{};
  auto var = std::ranges::find(names.mod.variables, name, &RtlirVariable::name);
  const DataType* written =
      var != names.mod.variables.end() ? var->written_type : nullptr;
  size_t dims = 0;
  bool aggregate_element = false;
  if (written != nullptr) {
    dims = var->num_unpacked_dims;
    std::vector<std::string_view> followed;
    aggregate_element =
        IsUnpackedAggregate(FollowTypedefs(*written, names.typedefs, followed));
  }
  for (size_t i = 0; i < std::min(dims, selects.size()); ++i)
    if (selects[i]->index_end != nullptr)
      return ForceVariableTarget::kAggregate;
  if (selects.size() != dims)
    return selects.size() > dims ? ForceVariableTarget::kBits
                                 : ForceVariableTarget::kAggregate;
  return aggregate_element ? ForceVariableTarget::kAggregate
                           : ForceVariableTarget::kSingular;
}

static void CheckForceVariableTarget(const Expr* e, const ForceLhsNames& names,
                                     SourceLoc loc, DiagEngine& diag) {
  switch (ClassifyForceVariableTarget(e, names)) {
    case ForceVariableTarget::kAggregate:
      diag.Error(loc,
                 "unpacked array, structure or union is not a legal force LHS",
                 Subclause("10.6.2"));
      break;
    case ForceVariableTarget::kBits:
      diag.Error(loc,
                 "bit-select or part-select of a variable is not a "
                 "legal force LHS",
                 Subclause("10.6.2"));
      break;
    default:
      break;
  }
}

static void CheckForceLhsOperand(const Expr* e, const ForceLhsNames& names,
                                 SourceLoc loc, DiagEngine& diag) {
  if (e->kind == ExprKind::kConcatenation) {
    for (auto* el : e->elements) CheckForceLhsOperand(el, names, loc, diag);
    return;
  }
  if (e->kind != ExprKind::kSelect && e->kind != ExprKind::kIdentifier) return;
  auto base_name = LhsBaseName(e);
  if (base_name.empty()) return;
  if (names.net_names.count(base_name) == 0) {
    CheckForceVariableTarget(e, names, loc, diag);
  } else if (e->kind != ExprKind::kSelect) {
    return;
  } else if (names.nettype_net_names.count(base_name) != 0) {
    diag.Error(loc,
               "bit-select or part-select of a net with a user-defined "
               "nettype is not a legal force LHS",
               Subclause("10.6.2"));
  } else if (!SelectPathIsConstant(e, names.scope)) {
    // §10.6.2 (printed page 257) admits a constant bit-select or constant
    // part-select of a vector net alone.
    diag.Error(loc,
               "bit-select or part-select of a net in a force LHS must be "
               "constant",
               Subclause("10.6.2"));
  }
}

// Reports §10.6.2's rule on what a force statement may name, at every statement
// position a force can stand in, which is what ForEachChildStmt enumerates.
void CheckForceLhs(const Stmt* s, const ForceLhsNames& names,
                   DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kForce && s->lhs)
    CheckForceLhsOperand(s->lhs, names, s->range.start, diag);
  ForEachChildStmt(s,
                   [&](const Stmt* sub) { CheckForceLhs(sub, names, diag); });
}

// True when any expression of `list` reads one of the named nets.
static bool AnyExprUsesInterconnect(
    const std::vector<Expr*>& list,
    const std::unordered_set<std::string_view>& names) {
  for (auto* sub : list)
    if (ExprUsesInterconnect(sub, names)) return true;
  return false;
}

bool ExprUsesInterconnect(const Expr* e,
                          const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier) return names.count(e->text) > 0;
  for (const Expr* sub : {e->lhs, e->rhs, e->condition, e->true_expr,
                          e->false_expr, e->base, e->index, e->index_end}) {
    if (ExprUsesInterconnect(sub, names)) return true;
  }
  return AnyExprUsesInterconnect(e->args, names) ||
         AnyExprUsesInterconnect(e->elements, names);
}

bool IsRealType(DataTypeKind k) {
  return k == DataTypeKind::kReal || k == DataTypeKind::kShortreal ||
         k == DataTypeKind::kRealtime;
}

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

using NameSet = std::unordered_set<std::string_view>;

static void CheckRealSelectNode(const Expr* e, const TypeMap& types,
                                const SelectOperands& operands,
                                DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  const bool kIsRealVar = !name.empty() && operands.variables.count(name) != 0;
  const bool kIsRealParam =
      !name.empty() && operands.parameters.count(name) != 0;
  if (kIsRealVar || kIsRealParam) {
    // §6.12 lists a bit-select or part-select reference of a real variable
    // among the cases in which real variables are prohibited, and §11.5.1
    // restates it and extends it to a scalar and to a real parameter. A real
    // variable is reported under §6.12, the clause that lists the prohibition,
    // and a real parameter under §11.5.1, the one clause that names it. The
    // sentence names two constructs, so the report names the construct that
    // was written and the operand it was written on. A select node carries
    // `index_end` for `[m:l]` and `is_part_select_plus` or
    // `is_part_select_minus` for `[b +: w]` and `[b -: w]`, the same three
    // fields CheckIndexedPartSelectWidthNode reads; a node with none of them
    // set is a bit-select.
    //
    // The two name sets are asked rather than the declared type of the operand,
    // because a real declared with an unpacked dimension is in neither set:
    // §11.5.2 makes indexing it an array element select, so
    // `real arr[4]; v = arr[i];` reads an element and is legal.
    const bool kIsBitSelect =
        !e->index_end && !e->is_part_select_plus && !e->is_part_select_minus;
    const char* const kConstruct = kIsBitSelect ? "bit-select" : "part-select";
    const char* const kOperand =
        kIsRealVar ? "real variable" : "real parameter";
    diag.Error(e->range.start,
               std::format("{} of a {} is illegal", kConstruct, kOperand),
               Subclause(kIsRealVar ? "6.12" : "11.5.1"));
    // Returning here leaves the index check below unreached for this node, so
    // `real a; real i; assign b = a[i];` draws the operand report alone. That
    // is deliberate: the operand breach already makes the whole select illegal
    // under the sentence above, and one construct drawing one report is what
    // this check exists to do.
    return;
  }
  if (!e->index) return;
  auto idx = ExprIdent(e->index);
  if (idx.empty()) return;
  auto it = types.find(idx);
  if (it != types.end() && IsRealType(it->second)) {
    // §6.12 lists a real index expression of a bit-select or part-select of a
    // vector among the prohibited cases; §11.5.1 only has the index be an
    // integer expression, so the citation is §6.12.
    diag.Error(e->range.start, "real type used as index is illegal",
               Subclause("6.12"));
  }
}

// §11.5.2: the name a chain of selects is written on, and how many addresses
// the chain carries. Parser::ParseSelectExpr in src/parser/expr_parser.cpp
// builds one ExprKind::kSelect node per bracketed address, so `arr[i][0]` is
// two nodes with the inner one standing as the outer one's `base`.
struct SelectChain {
  std::string_view name;
  size_t addresses = 0;
};

static SelectChain ResolveSelectChain(const Expr* e) {
  SelectChain chain;
  const Expr* n = e;
  while (n && n->kind == ExprKind::kSelect) {
    ++chain.addresses;
    n = n->base;
  }
  if (n && n->kind == ExprKind::kIdentifier) chain.name = n->text;
  return chain;
}

// §11.5.1 reached through §11.5.2: report an address written one past the
// dimensions of the declaration the chain stands on. §11.5.2 has the word
// selected first, one address per dimension, and the select that follows
// addressed as a net's or a variable's select is (§11.5.1), so
// `real arr[4]; v = arr[i][0];` is the bit-select of a real that sentence bars,
// and `logic [7:0] mem[4]; v = mem[i][0];` is the legal case the same sentence
// exists to permit.
static void CheckElementSelectNode(const Expr* e, const SelectShapeMap& shapes,
                                   DiagEngine& diag) {
  // Only a chain of two or more addresses is judged here. A select carrying one
  // address is the case CheckRealSelectNode and CheckScalarSelectNode already
  // report from the name sets, and judging it here as well would make one
  // breach draw two reports.
  if (!e->base || e->base->kind != ExprKind::kSelect) return;
  SelectChain chain = ResolveSelectChain(e);
  if (chain.name.empty()) return;
  auto it = shapes.find(chain.name);
  if (it == shapes.end()) return;
  // Exactly the first address past the last dimension is reported. A longer
  // chain addresses bits of that bit, which this one report already stands for.
  if (chain.addresses != it->second.addressable_dims + 1) return;
  const bool kIsBitSelect =
      !e->index_end && !e->is_part_select_plus && !e->is_part_select_minus;
  // The real element is reported under §6.12, as CheckRealSelectNode reports a
  // real declared without the dimension, since the element is a real variable
  // and §6.12 is the clause that lists the prohibition; the scalar element is
  // reported under §11.5.1, which alone names a scalar.
  if (it->second.element_is_real) {
    diag.Error(e->range.start,
               std::format("{} of a real variable is illegal",
                           kIsBitSelect ? "bit-select" : "part-select"),
               Subclause("6.12"));
    return;
  }
  if (it->second.element_is_scalar) {
    diag.Error(e->range.start,
               "bit-select or part-select of a scalar is illegal",
               Subclause("11.5.1"));
  }
}

void CheckRealSelect(const Expr* e, const TypeMap& types,
                     const SelectOperands& operands, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base) {
    CheckRealSelectNode(e, types, operands, diag);
    // The element-select case rides this walk rather than one of its own,
    // because it is judged at the same nodes and both alternatives of
    // §11.5.1's sentence are reported from here.
    CheckElementSelectNode(e, operands.shapes, diag);
  }
  ForEachExprChild(e, [&](const Expr* child) {
    CheckRealSelect(child, types, operands, diag);
  });
}

static void CheckScalarSelectNode(const Expr* e, const NameSet& scalars,
                                  DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  if (name.empty()) return;
  if (scalars.count(name) != 0)
    diag.Error(e->range.start,
               "bit-select or part-select of a scalar is illegal",
               Subclause("11.5.1"));
}

void CheckScalarSelect(const Expr* e, const NameSet& scalars,
                       DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base)
    CheckScalarSelectNode(e, scalars, diag);
  ForEachExprChild(
      e, [&](const Expr* child) { CheckScalarSelect(child, scalars, diag); });
}

static void CheckIndexedPartSelectWidthNode(const Expr* e,
                                            const ScopeMap& scope,
                                            DiagEngine& diag) {
  if (!e->index_end) return;
  if (!e->is_part_select_plus && !e->is_part_select_minus) return;
  // §11.5.1: the width is a constant expression, which per §11.2.1 may be a
  // parameter/localparam reference. Evaluate it in the module's parameter scope
  // so `x[i +: WIDTH]` resolves rather than being rejected as non-constant.
  auto width = ConstEvalInt(e->index_end, scope);
  if (!width.has_value()) {
    diag.Error(e->range.start,
               "indexed part-select width must be a constant expression",
               Subclause("11.5.1"));
    return;
  }
  // §11.5.1 requires the width of an indexed part-select to be positive.
  if (*width <= 0)
    diag.Error(e->range.start,
               "indexed part-select width must be a positive constant",
               Subclause("11.5.1"));
}

void CheckIndexedPartSelectWidth(const Expr* e, const ScopeMap& scope,
                                 DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base)
    CheckIndexedPartSelectWidthNode(e, scope, diag);
  ForEachExprChild(e, [&](const Expr* child) {
    CheckIndexedPartSelectWidth(child, scope, diag);
  });
}

void CheckScalarSelectStmt(const Stmt* s, const NameSet& scalars,
                           DiagEngine& diag) {
  if (!s) return;
  CheckScalarSelect(s->lhs, scalars, diag);
  CheckScalarSelect(s->rhs, scalars, diag);
  CheckScalarSelect(s->expr, scalars, diag);
  CheckScalarSelect(s->condition, scalars, diag);
  CheckScalarSelect(s->for_cond, scalars, diag);
  ForEachChildStmt(
      s, [&](const Stmt* sub) { CheckScalarSelectStmt(sub, scalars, diag); });
}

// §11.5.1 applies to a select written in a procedural statement exactly as it
// applies to one written on a continuous assignment. The real-operand check
// reaches every statement position CheckScalarSelectStmt reaches because both
// recurse through ForEachChildStmt.
void CheckRealSelectStmt(const Stmt* s, const TypeMap& types,
                         const SelectOperands& operands, DiagEngine& diag) {
  if (!s) return;
  CheckRealSelect(s->lhs, types, operands, diag);
  CheckRealSelect(s->rhs, types, operands, diag);
  CheckRealSelect(s->expr, types, operands, diag);
  CheckRealSelect(s->condition, types, operands, diag);
  CheckRealSelect(s->for_cond, types, operands, diag);
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckRealSelectStmt(sub, types, operands, diag);
  });
}

void CheckIndexedPartSelectWidthStmt(const Stmt* s, const ScopeMap& scope,
                                     DiagEngine& diag) {
  if (!s) return;
  CheckIndexedPartSelectWidth(s->lhs, scope, diag);
  CheckIndexedPartSelectWidth(s->rhs, scope, diag);
  CheckIndexedPartSelectWidth(s->expr, scope, diag);
  CheckIndexedPartSelectWidth(s->condition, scope, diag);
  CheckIndexedPartSelectWidth(s->for_cond, scope, diag);
  ForEachChildStmt(s, [&](const Stmt* sub) {
    CheckIndexedPartSelectWidthStmt(sub, scope, diag);
  });
}

bool ExprContainsIdent(const Expr* e, std::string_view name) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == name) return true;
  return AnyExprChild(
      e, [name](const Expr* child) { return ExprContainsIdent(child, name); });
}

NettypeResolutionRule ValidateNettypeResolutionFunction(
    const NettypeResolutionSig& sig) {
  // The requirements §6.6.7 states, one test each, returned in the order the
  // clause writes them: a function returning T, taking one input argument that
  // is a dynamic array of T elements, and automatic or keeping no state. The
  // first one broken is what the caller reports, so a signature breaking
  // several names the first rather than all of them.
  if (!sig.return_type_matches_nettype)
    return NettypeResolutionRule::kReturnType;
  if (!sig.single_input_argument) return NettypeResolutionRule::kArgumentCount;
  if (!sig.argument_is_input) return NettypeResolutionRule::kArgumentDirection;
  if (!sig.argument_is_dynamic_array)
    return NettypeResolutionRule::kArgumentIsDynamicArray;
  if (!sig.argument_element_type_matches)
    return NettypeResolutionRule::kArgumentElementType;
  if (!sig.is_automatic) return NettypeResolutionRule::kAutomaticLifetime;
  // A class method is admissible only when it is static, because the resolution
  // call occurs with no class object involved.
  if (sig.is_class_method && !sig.is_static_method)
    return NettypeResolutionRule::kClassStaticMethod;
  return NettypeResolutionRule::kConforming;
}

}  // namespace delta
