#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_constraints.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

// 18.4: a real variable may be rand, never randc. The randc cyclic semantics
// are defined only over an integral declared range, so a real property may
// carry rand but never randc.
static bool IsRealDataType(DataTypeKind kind) {
  return kind == DataTypeKind::kReal || kind == DataTypeKind::kShortreal ||
         kind == DataTypeKind::kRealtime;
}

// Builds a name->member map of the class properties visible in `cls`, walking
// the base-class chain so that a derived declaration shadows a base one (the
// most-derived binding is kept).
static std::unordered_map<std::string_view, const ClassMember*>
BuildClassPropertyMap(const ClassDecl* cls, const CompilationUnit* unit) {
  std::unordered_map<std::string_view, const ClassMember*> properties;
  for (const ClassDecl* c = cls; c; c = FindBaseClass(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name.empty()) continue;
      properties.emplace(m->name, m);  // keeps the most-derived binding
    }
  }
  return properties;
}

// Resolve a declared type through any typedef chain (bounded) so an aggregate
// hidden behind a named type is still examined.
static const DataType* ResolveThroughTypedefs(const DataType* dt,
                                              const TypedefMap& typedefs) {
  for (int hops = 0; hops < 8 && dt->kind == DataTypeKind::kNamed; ++hops) {
    auto it = typedefs.find(dt->type_name);
    if (it == typedefs.end()) break;
    dt = &it->second;
  }
  return dt;
}

// 18.4: validate the aggregate-rand restrictions on a single rand/randc
// property. Resolves the declared type through any typedef chain so that a
// union or structure hidden behind a named type is still examined, then rejects
// the non-randomizable flavors.
static void ValidateRandAggregateMember(const ClassMember* m,
                                        const TypedefMap& typedefs,
                                        DiagEngine& diag) {
  const DataType* resolved = ResolveThroughTypedefs(&m->data_type, typedefs);
  // Only a packed untagged union may be randomized: it is treated as an
  // integral value. An unpacked union has no single integral image, and a
  // packed tagged union carries a tag that randomization cannot honor.
  if (resolved->kind == DataTypeKind::kUnion) {
    if (!resolved->is_packed) {
      diag.Error(m->loc,
                 std::format("unpacked union '{}' takes neither the rand nor "
                             "the randc qualifier",
                             m->name),
                 Subclause("18.4"));
    } else if (resolved->is_tagged) {
      diag.Error(m->loc,
                 std::format("packed tagged union '{}' takes neither the rand "
                             "nor the randc qualifier",
                             m->name),
                 Subclause("18.4"));
    }
    return;
  }
  // An unpacked structure may be declared rand (its random members are solved
  // concurrently), though never randc: randc cycles over a single
  // integral declared range, which an unpacked aggregate does not present. A
  // packed structure is treated as an integral value, so randc is allowed there
  // and is not rejected here.
  if (m->is_randc && resolved->kind == DataTypeKind::kStruct &&
      !resolved->is_packed) {
    diag.Error(m->loc,
               std::format("unpacked structure '{}' can be rand but not randc",
                           m->name),
               Subclause("18.4"));
  }
}

void ClassConstraintValidator::ValidateOneClassRandomVariables(
    const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kProperty) continue;
    const DataType& dt = m->data_type;

    // §18.4 lets a real variable be rand, never randc.
    if (m->is_randc && IsRealDataType(dt.kind)) {
      diag_.Error(
          m->loc,
          std::format("real variable '{}' can be rand but not randc", m->name),
          Subclause("18.4"));
    }

    // An object handle may be declared rand but never randc: randomization
    // solves the referenced object's variables and never reassigns the handle
    // itself, so there is no cyclic value sequence for randc to permute.
    if (m->is_randc && dt.kind == DataTypeKind::kNamed &&
        FindClassDecl(dt.type_name, unit_) != nullptr) {
      diag_.Error(
          m->loc,
          std::format("object handle '{}' can be rand but not randc", m->name),
          Subclause("18.4"));
    }

    if (m->is_rand || m->is_randc)
      ValidateRandAggregateMember(m, typedefs_, diag_);
  }
}

void ClassConstraintValidator::ValidateRandomVariableTypes() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassRandomVariables(cls);
}

// 18.5: no two constraint blocks of one class may share a name.
void ClassConstraintValidator::ValidateOneClassConstraintNames(
    const ClassDecl* cls) {
  std::unordered_set<std::string_view> seen;
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (m->name.empty()) continue;
    if (!seen.insert(m->name).second) {
      diag_.Error(m->loc,
                  std::format("constraint block name '{}' is not unique "
                              "within class '{}'",
                              m->name, cls->name),
                  Subclause("18.5"));
    }
  }
}

void ClassConstraintValidator::ValidateConstraintBlockNames() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassConstraintNames(cls);
}

// 18.5.7.1: the dimension count of a class property whose dimensions are fully
// visible on its declaration — its packed dimensions plus its unpacked
// dimensions.
static int ConstraintArrayDimCount(const ClassMember* m) {
  int packed = (m->data_type.packed_dim_left != nullptr ? 1 : 0) +
               static_cast<int>(m->data_type.extra_packed_dims.size());
  int unpacked = static_cast<int>(m->unpacked_dims.size());
  return packed + unpacked;
}

// 18.5.7.1: a leaf scalar type — integral/vector or real — whose array
// dimensionality is determined entirely by its own declaration. The
// loop-variable-count check is confined to these so that a typedef'd or
// aggregate element type, which may contribute packed dimensions not visible at
// the array declaration, is conservatively left alone. A real type carries no
// packed dimensions, so a real array's dimension count is exactly as visible as
// an integral array's; the foreach rule applies to it just the same (rand real
// arrays are legal random variables).
static bool IsFullyVisibleDimensionKind(DataTypeKind k) {
  switch (k) {
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
    case DataTypeKind::kInteger:
    case DataTypeKind::kTime:
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
      return true;
    default:
      return false;
  }
}

// 18.5.7.1: a foreach iterative constraint names no more loop variables than
// the iterated array has dimensions. The array is a class property, possibly
// inherited, so resolve the name through the class and its base-class chain; a
// derived declaration shadows a base one. Only leaf-scalar arrays
// (integral/vector or real) with at least one dimension are checked, which
// excludes scalars (not array variables, hence outside this rule) and complex
// types whose dimensionality is not fully visible.
// 18.5.7.1: check a single foreach iterative-constraint reference against the
// resolved class properties, reporting when its loop-variable count exceeds the
// dimension count of the named array.
static void CheckOneForeachConstraintRef(
    const ConstraintForeachRef& fe,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    DiagEngine& diag) {
  auto it = properties.find(fe.array_name);
  if (it == properties.end()) return;
  if (!IsFullyVisibleDimensionKind(it->second->data_type.kind)) return;
  int dims = ConstraintArrayDimCount(it->second);
  if (dims < 1) return;  // not an array variable: not this rule's concern
  if (fe.loop_var_count > dims) {
    diag.Error(
        fe.loc,
        std::format("foreach iterative constraint lists {} loop "
                    "variable(s) but array '{}' has only {} dimension(s)",
                    fe.loop_var_count, fe.array_name, dims),
        Subclause("18.5.7.1"));
  }
}

void ClassConstraintValidator::ValidateOneClassForeachConstraintDims(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& fe : m->constraint_foreach_refs)
      CheckOneForeachConstraintRef(fe, properties, diag_);
  }
}

void ClassConstraintValidator::ValidateForeachConstraintDims() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassForeachConstraintDims(cls);
}

// 18.5.3 lists among its limitations that a dist operation is not applied to a
// randc variable. Both the qualifier and the distribution are declarations, so
// the breach is decided from the class text and reported here, at the
// distributed variable, rather than left to a randomize() call, which a design
// that never randomizes the object would not reach.
//
// 18.5.3 also requires that a range of real values in a distribution use the :/
// operator and specify a weight. When the distributed variable is real-typed,
// every range item of its distribution is a real-valued range, so it may
// neither use
// := (which spreads the weight per element — meaningful only for an integral
// range) nor omit its weight. The parser records both offending forms with
// per_element set: an explicit := range, and a bare range that defaults to := 1
// with no weight. A real range whose per_element flag is set therefore violates
// the rule and is rejected; a :/ range (per_element clear, weight always
// present) is accepted. The target is resolved against the class property map
// so an inherited randc or real member is recognized.
static void CheckOneDistConstraintRef(
    const ConstraintDistRef& ref,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    DiagEngine& diag) {
  if (ref.target == nullptr || ref.target->kind != ExprKind::kIdentifier)
    return;
  auto it = properties.find(ref.target->text);
  if (it == properties.end()) return;
  if (it->second->is_randc) {
    diag.Error(ref.target->range.start,
               std::format("a dist constraint may not be applied to randc "
                           "variable '{}'",
                           ref.target->text),
               Subclause("18.5.3"));
  }
  if (!IsRealDataType(it->second->data_type.kind)) return;
  for (const auto& item : ref.items) {
    if (!item.is_range || !item.per_element) continue;
    SourceLoc loc =
        item.lo != nullptr ? item.lo->range.start : ref.target->range.start;
    diag.Error(loc,
               "a real-valued range in a dist constraint requires the :/ "
               "operator and an explicit weight",
               Subclause("18.5.3"));
  }
}

void ClassConstraintValidator::ValidateOneClassDistConstraints(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_dist_refs)
      CheckOneDistConstraintRef(ref, properties, diag_);
  }
}

void ClassConstraintValidator::ValidateDistConstraints() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassDistConstraints(cls);
}

// 18.5.4 / footnote 13: a range_list member of a uniqueness constraint denotes
// a variable when it is a bare name (a singular or whole-array variable), an
// element or slice select of one (an array variable — descend through the
// possibly nested selects to the base), or a member/scope-qualified name. Any
// other expression shape — a literal, an arithmetic expression, a call —
// denotes no variable.
static bool UniqueMemberDenotesVariable(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return e != nullptr && (e->kind == ExprKind::kIdentifier ||
                          e->kind == ExprKind::kMemberAccess);
}

// 18.5.4: the identifier of the variable a range_list member denotes — a bare
// name, or an element/slice select of an array (descend the select chain to its
// base). Empty for a member-access-qualified name or any non-variable shape,
// which the type check then leaves alone.
static std::string_view UniqueMemberBaseName(const Expr* e) {
  while (e != nullptr && e->kind == ExprKind::kSelect) e = e->base;
  return (e != nullptr && e->kind == ExprKind::kIdentifier)
             ? e->text
             : std::string_view{};
}

// 18.5.4 and 18.5.9: a variable named in a uniqueness group or a solve...before
// ordering shall be of integral or real type. Reject the types that are plainly
// neither -- strings, events, chandles, virtual interfaces, void, and class
// handles. A typedef name is left alone (its underlying type is assumed
// orderable), keeping the check conservative so it never flags a legitimate
// integral or real variable.
static bool IsSolveOrderableTypeFree(const DataType& dt,
                                     const CompilationUnit* unit) {
  switch (dt.kind) {
    case DataTypeKind::kString:
    case DataTypeKind::kEvent:
    case DataTypeKind::kChandle:
    case DataTypeKind::kVirtualInterface:
    case DataTypeKind::kVoid:
      return false;
    case DataTypeKind::kNamed:
      return FindClassDecl(dt.type_name, unit) == nullptr;
    default:
      return true;
  }
}

// 18.5.4 / footnote 13: the range_list of a uniqueness constraint shall contain
// only expressions that denote singular or array variables, and each such
// member shall be of integral or real type — for an array member, its leaf
// element type. Reject a member that denotes no variable (so the group is a
// well-formed set of variables) and a member whose resolved type is plainly
// neither integral nor real, and, as no randc variable shall appear in the
// group, a member that names a randc variable. The type check resolves a plain
// local identifier —
// or the base array of a select — against the class property map (walking the
// base-class chain); a member-access-qualified or unresolved reference is left
// alone, keeping the check conservative so it never flags a legitimate integral
// or real variable. The integral-or-real test is the same one solve...before
// ordering uses.
static void ValidateOneUniqueConstraintMember(
    const Expr* mem,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (mem == nullptr) return;
  if (!UniqueMemberDenotesVariable(mem)) {
    diag.Error(mem->range.start,
               "a uniqueness constraint member shall denote a singular "
               "or array variable",
               Subclause("18.5.4"));
    return;
  }
  std::string_view base = UniqueMemberBaseName(mem);
  if (base.empty()) return;
  auto it = properties.find(base);
  if (it == properties.end()) return;
  if (it->second->is_randc) {
    diag.Error(mem->range.start,
               "a uniqueness constraint member shall not be a randc variable",
               Subclause("18.5.4"));
  }
  if (!IsSolveOrderableTypeFree(it->second->data_type, unit)) {
    diag.Error(mem->range.start,
               "a uniqueness constraint member shall be of integral or "
               "real type",
               Subclause("18.5.4"));
  }
}

// Checks every member of each uniqueness group `block` holds.
static void ValidateUniqueGroups(
    const ClassMember* block,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    const CompilationUnit* unit, DiagEngine& diag) {
  for (const auto& group : block->constraint_unique_refs) {
    for (const Expr* mem : group)
      ValidateOneUniqueConstraintMember(mem, properties, unit, diag);
  }
}

void ValidateInlineUniqueGroups(const Expr* call, const ClassDecl* cls,
                                const CompilationUnit* unit, DiagEngine& diag) {
  if (call->inline_constraint == nullptr) return;
  ValidateUniqueGroups(call->inline_constraint,
                       BuildClassPropertyMap(cls, unit), unit, diag);
}

void ClassConstraintValidator::ValidateOneClassUniqueConstraints(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint) {
      ValidateUniqueGroups(m, properties, unit_, diag_);
    }
  }
}

void ClassConstraintValidator::ValidateUniqueConstraints() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassUniqueConstraints(cls);
  ValidateInlineUniqueReceivers(unit_, diag_);
}

// 18.3: the class properties a constraint reads and where its findings go.
struct ConstraintOperandScope {
  std::unordered_map<std::string_view, const ClassMember*> properties;
  const CompilationUnit* unit;
  DiagEngine& diag;
};

// 18.3: whether `e` is plainly of a type neither integral nor real -- a cast
// to string, a property of a type IsSolveOrderableTypeFree
// rejects, $sformatf, which yields a string, or a conditional with such an
// arm, whose result takes the arm's type. Any other shape is taken to be
// integral or real, so the check never flags a legitimate constraint.
static bool PlainlyNeitherIntegralNorReal(const Expr* e,
                                          const ConstraintOperandScope& s) {
  if (e->kind == ExprKind::kCast) return e->text == "string";
  if (e->kind == ExprKind::kIdentifier) {
    const auto kFound = s.properties.find(e->text);
    return kFound != s.properties.end() &&
           !IsSolveOrderableTypeFree(kFound->second->data_type, s.unit);
  }
  if (e->kind == ExprKind::kTernary) {
    return PlainlyNeitherIntegralNorReal(e->true_expr, s) ||
           PlainlyNeitherIntegralNorReal(e->false_expr, s);
  }
  return e->kind == ExprKind::kSystemCall && e->text == "$sformatf";
}

// 18.3: whether `e` reads a random variable of the solve -- a rand or randc
// property of an integral or real type. A random object handle is none: its
// object's variables are solved, never the handle.
static bool HoldsRandomVariable(const Expr* e,
                                const ConstraintOperandScope& s) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) {
    const auto kFound = s.properties.find(e->text);
    if (kFound == s.properties.end()) return false;
    const ClassMember* m = kFound->second;
    return (m->is_rand || m->is_randc) &&
           IsSolveOrderableTypeFree(m->data_type, s.unit);
  }
  bool holds = false;
  ForEachExprChild(e, [&](const Expr* child) {
    holds = holds || HoldsRandomVariable(child, s);
  });
  return holds;
}

// 18.3: a constraint's operands are integral or real; a subexpression of
// another type is allowed only where it holds no random variable. The
// outermost such subexpression is reported, and nothing under it.
static void CheckConstraintOperands(const Expr* e,
                                    const ConstraintOperandScope& s) {
  if (e == nullptr) return;
  if (PlainlyNeitherIntegralNorReal(e, s) && HoldsRandomVariable(e, s)) {
    s.diag.Error(e->range.start,
                 "a constraint subexpression holding a random variable shall "
                 "be of an integral or real type",
                 Subclause("18.3"));
    return;
  }
  ForEachExprChild(
      e, [&](const Expr* child) { CheckConstraintOperands(child, s); });
}

static void CheckConstraintItemOperands(
    const std::vector<ConstraintItem*>& items,
    const ConstraintOperandScope& s) {
  for (const ConstraintItem* item : items) {
    CheckConstraintOperands(item->expr, s);
    for (const Expr* e : item->exprs) CheckConstraintOperands(e, s);
    for (const Expr* e : item->after) CheckConstraintOperands(e, s);
    CheckConstraintItemOperands(item->body, s);
    CheckConstraintItemOperands(item->else_body, s);
  }
}

void ValidateInlineConstraintOperands(const Expr* call, const ClassDecl* cls,
                                      const CompilationUnit* unit,
                                      DiagEngine& diag) {
  const ConstraintOperandScope kScope{BuildClassPropertyMap(cls, unit), unit,
                                      diag};
  CheckConstraintItemOperands(call->inline_constraint->constraint_items,
                              kScope);
}

void ClassConstraintValidator::ValidateConstraintOperandTypes() {
  for (const auto* cls : AllClassDecls(unit_)) {
    const ConstraintOperandScope kScope{BuildClassPropertyMap(cls, unit_),
                                        unit_, diag_};
    for (const auto* m : cls->members) {
      if (m->kind == ClassMemberKind::kConstraint) {
        CheckConstraintItemOperands(m->constraint_items, kScope);
      }
    }
  }
}

// 18.5.9: the restrictions that apply to solve...before variable ordering:
//   - only random variables are allowed (they shall be rand);
//   - randc variables are not allowed (they are always solved before any
//   other);
//   - the variables shall be integral or real;
//   - there shall be no circular dependency in the ordering.
// As with the foreach dimension check, resolve each named variable against the
// class and its base chain (a derived declaration shadows a base one), and
// apply the rand/integral restrictions only to simple local identifiers that
// resolve to a property — a hierarchical reference or an array.size() method
// (expressly allowed as an ordering variable) is left alone.
// Add the ordering edges contributed by a single solve...before reference to
// the aggregate graph. Build the graph only over plain variable names: a
// qualified or array-method primary (e.g. two different arrays' size() both
// reduce to the leaf 'size') could otherwise collide into a spurious cycle.
static void AddSolveBeforeEdges(
    const ConstraintSolveBeforeRef& ref,
    std::unordered_map<std::string_view, std::vector<std::string_view>>& succ,
    std::unordered_set<std::string_view>& nodes) {
  for (const auto& b : ref.before) {
    if (!b.is_simple) continue;
    for (const auto& a : ref.after) {
      if (!a.is_simple) continue;
      succ[b.name].push_back(a.name);
      nodes.insert(b.name);
      nodes.insert(a.name);
    }
  }
}

// Depth-first visit of one node in a solve...before ordering graph, used by
// SolveBeforeGraphHasCycle. Colors: 0 white, 1 gray (on stack), 2 black.
// Returns true as soon as a gray successor is reached, which closes a cycle.
static bool SolveBeforeVisit(
    std::string_view v,
    const std::unordered_map<std::string_view, std::vector<std::string_view>>&
        succ,
    std::unordered_map<std::string_view, int>& color) {
  color[v] = 1;
  auto sit = succ.find(v);
  if (sit != succ.end()) {
    for (std::string_view w : sit->second) {
      if (color[w] == 1) return true;
      if (color[w] == 0 && SolveBeforeVisit(w, succ, color)) return true;
    }
  }
  color[v] = 2;
  return false;
}

// Depth-first cycle detection over a solve...before ordering graph. A gray
// (on-stack) successor closes a cycle, such as 'solve a before b' combined with
// 'solve b before a' (or a degenerate 'solve a before a').
static bool SolveBeforeGraphHasCycle(
    const std::unordered_map<std::string_view, std::vector<std::string_view>>&
        succ,
    const std::unordered_set<std::string_view>& nodes) {
  std::unordered_map<std::string_view, int> color;  // 0 white, 1 gray, 2 black
  for (std::string_view v : nodes) {
    if (color[v] == 0 && SolveBeforeVisit(v, succ, color)) return true;
  }
  return false;
}

// 18.5.9: resolve one solve...before entry to the local property it names and
// emit the rand/randc diagnostics. Returns the resolved property when 'e' is a
// simple local rand variable still needing the integral/real-type check, or
// nullptr when there is nothing further to check (not simple, not a local
// property, or already reported as randc/non-rand).
static const ClassMember* ResolveSolveBeforeEntry(
    const ConstraintSolveBeforeEntry& e, const SourceLoc& loc,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    DiagEngine& diag) {
  if (!e.is_simple)
    return nullptr;  // hierarchical ref or array.size(): allowed
  auto it = properties.find(e.name);
  if (it == properties.end()) return nullptr;  // not a local property
  const ClassMember* prop = it->second;
  if (prop->is_randc) {
    diag.Error(loc,
               std::format("randc variable '{}' is not allowed in a "
                           "solve...before ordering constraint",
                           e.name),
               Subclause("18.5.9"));
    return nullptr;
  }
  if (!prop->is_rand) {
    diag.Error(loc,
               std::format("'{}' is not a random variable and cannot "
                           "appear in a solve...before ordering "
                           "constraint",
                           e.name),
               Subclause("18.5.9"));
    return nullptr;
  }
  return prop;
}

// The aggregate solve...before ordering graph for one class, collected across
// all of its constraint blocks so a circular dependency that spans more than
// one solve statement is still detected. 'report_loc' is the location of the
// first ordering reference, used to anchor a circular-dependency diagnostic.
struct SolveBeforeOrdering {
  std::unordered_map<std::string_view, std::vector<std::string_view>> succ;
  std::unordered_set<std::string_view> nodes;
  bool have_loc = false;
  SourceLoc report_loc;
};

// 18.5.9: resolve one solve...before entry and emit the rand/randc and
// integral/real-type diagnostics for it.
static void CheckSolveBeforeEntry(
    const ConstraintSolveBeforeEntry& e, const SourceLoc& loc,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    const CompilationUnit* unit, DiagEngine& diag) {
  const ClassMember* prop = ResolveSolveBeforeEntry(e, loc, properties, diag);
  if (prop && !IsSolveOrderableTypeFree(prop->data_type, unit)) {
    diag.Error(loc,
               std::format("solve...before ordering variable '{}' shall be "
                           "of integral or real type",
                           e.name),
               Subclause("18.5.9"));
  }
}

// 18.5.9: fold one solve...before reference into the class ordering: emit the
// per-entry rand/randc/type diagnostics and accumulate its ordering edges.
static void CollectSolveBeforeRef(
    const ConstraintSolveBeforeRef& ref,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    const CompilationUnit* unit, DiagEngine& diag, SolveBeforeOrdering& order) {
  if (!order.have_loc) {
    order.report_loc = ref.loc;
    order.have_loc = true;
  }
  for (const auto& e : ref.before)
    CheckSolveBeforeEntry(e, ref.loc, properties, unit, diag);
  for (const auto& e : ref.after)
    CheckSolveBeforeEntry(e, ref.loc, properties, unit, diag);
  AddSolveBeforeEdges(ref, order.succ, order.nodes);
}

void ClassConstraintValidator::ValidateOneClassSolveBeforeConstraints(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);

  SolveBeforeOrdering order;
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_solve_before_refs)
      CollectSolveBeforeRef(ref, properties, unit_, diag_, order);
  }

  if (SolveBeforeGraphHasCycle(order.succ, order.nodes)) {
    diag_.Error(order.report_loc,
                "circular dependency in solve...before variable ordering",
                Subclause("18.5.9"));
  }
}

void ClassConstraintValidator::ValidateSolveBeforeConstraints() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassSolveBeforeConstraints(cls);
}

// 18.5.13.1: a soft constraint applies to random variables alone, and never to
// a randc variable. Resolve each bare local variable named in a soft constraint
// expression against the class and its base chain (a derived declaration
// shadows a base one) and reject one that resolves to a randc property. As with
// the solve...before and foreach checks, only simple local identifiers the
// parser recorded are considered; a qualified reference or one that does not
// resolve to a local property is left alone.
void ClassConstraintValidator::ValidateOneClassSoftConstraintVariables(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_soft_refs) {
      auto it = properties.find(ref.name);
      if (it == properties.end()) continue;  // not a local property
      if (it->second->is_randc) {
        diag_.Error(ref.loc,
                    std::format("a soft constraint may not be specified on "
                                "randc variable '{}'",
                                ref.name),
                    Subclause("18.5.13.1"));
      }
    }
  }
}

void ClassConstraintValidator::ValidateSoftConstraintVariables() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassSoftConstraintVariables(cls);
}

}  // namespace delta
