#include <algorithm>
#include <format>
#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_constraints.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

// 18.4: a real variable shall not be declared randc. The randc cyclic
// semantics are defined only over an integral declared range, so a real
// property may carry rand but never randc.
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
  for (const ClassDecl* c = cls; c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
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
                 std::format("unpacked union '{}' shall not be declared "
                             "rand or randc",
                             m->name));
    } else if (resolved->is_tagged) {
      diag.Error(m->loc, std::format("packed tagged union '{}' shall not be "
                                     "declared rand or randc",
                                     m->name));
    }
    return;
  }
  // An unpacked structure may be declared rand (its random members are solved
  // concurrently), but shall not be declared randc: randc cycles over a single
  // integral declared range, which an unpacked aggregate does not present. A
  // packed structure is treated as an integral value, so randc is allowed there
  // and is not rejected here.
  if (m->is_randc && resolved->kind == DataTypeKind::kStruct &&
      !resolved->is_packed) {
    diag.Error(m->loc, std::format("unpacked structure '{}' shall not be "
                                   "declared randc",
                                   m->name));
  }
}

void ClassConstraintValidator::ValidateOneClassRandomVariables(
    const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kProperty) continue;
    const DataType& dt = m->data_type;

    // A real variable shall not be declared randc.
    if (m->is_randc && IsRealDataType(dt.kind)) {
      diag_.Error(m->loc,
                  std::format("real variable '{}' shall not be declared randc",
                              m->name));
    }

    // An object handle may be declared rand but never randc: randomization
    // solves the referenced object's variables and never reassigns the handle
    // itself, so there is no cyclic value sequence for randc to permute.
    if (m->is_randc && dt.kind == DataTypeKind::kNamed &&
        FindClassDecl(dt.type_name, unit_) != nullptr) {
      diag_.Error(m->loc,
                  std::format("object handle '{}' shall not be declared randc",
                              m->name));
    }

    if (m->is_rand || m->is_randc)
      ValidateRandAggregateMember(m, typedefs_, diag_);
  }
}

void ClassConstraintValidator::ValidateRandomVariableTypes() {
  for (const auto* cls : unit_->classes) ValidateOneClassRandomVariables(cls);
}

// 18.5: constraint block names shall be unique within a class.
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
                              m->name, cls->name));
    }
  }
}

void ClassConstraintValidator::ValidateConstraintBlockNames() {
  for (const auto* cls : unit_->classes) ValidateOneClassConstraintNames(cls);
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

// 18.5.7.1: in a foreach iterative constraint the number of loop variables
// shall not exceed the number of dimensions of the iterated array. The array is
// a class property, possibly inherited, so resolve the name through the class
// and its base-class chain; a derived declaration shadows a base one. Only
// leaf-scalar arrays (integral/vector or real) with at least one dimension are
// checked, which excludes scalars (not array variables, hence outside this
// rule) and complex types whose dimensionality is not fully visible.
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
                    fe.loop_var_count, fe.array_name, dims));
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
  for (const auto* cls : unit_->classes)
    ValidateOneClassForeachConstraintDims(cls);
}

// 18.5.3: a range of real values in a distribution shall use the :/ operator
// and shall specify a weight. When the distributed variable is real-typed,
// every range item of its distribution is a real-valued range, so it may
// neither use
// := (which spreads the weight per element — meaningful only for an integral
// range) nor omit its weight. The parser records both offending forms with
// per_element set: an explicit := range, and a bare range that defaults to := 1
// with no weight. A real range whose per_element flag is set therefore violates
// the rule and is rejected; a :/ range (per_element clear, weight always
// present) is accepted. The target is resolved against the class property map
// so an inherited real member is recognized.
static void CheckOneDistConstraintRef(
    const ConstraintDistRef& ref,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    DiagEngine& diag) {
  if (ref.target == nullptr || ref.target->kind != ExprKind::kIdentifier)
    return;
  auto it = properties.find(ref.target->text);
  if (it == properties.end()) return;
  if (!IsRealDataType(it->second->data_type.kind)) return;
  for (const auto& item : ref.items) {
    if (!item.is_range || !item.per_element) continue;
    SourceLoc loc =
        item.lo != nullptr ? item.lo->range.start : ref.target->range.start;
    diag.Error(loc,
               "a real-valued range in a dist constraint requires the :/ "
               "operator and an explicit weight");
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
  for (const auto* cls : unit_->classes) ValidateOneClassDistConstraints(cls);
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

// 18.5.4 / footnote 13: the range_list of a uniqueness constraint shall contain
// only expressions that denote singular or array variables, and each such
// member shall be of integral or real type — for an array member, its leaf
// element type. Reject a member that denotes no variable (so the group is a
// well-formed set of variables) and a member whose resolved type is plainly
// neither integral nor real. The type check resolves a plain local identifier —
// or the base array of a select — against the class property map (walking the
// base-class chain); a member-access-qualified or unresolved reference is left
// alone, keeping the check conservative so it never flags a legitimate integral
// or real variable. The integral-or-real test is the same one solve...before
// ordering uses.
void ClassConstraintValidator::ValidateOneUniqueConstraintMember(
    const Expr* mem,
    const std::unordered_map<std::string_view, const ClassMember*>&
        properties) {
  if (mem == nullptr) return;
  if (!UniqueMemberDenotesVariable(mem)) {
    diag_.Error(mem->range.start,
                "a uniqueness constraint member shall denote a singular "
                "or array variable");
    return;
  }
  std::string_view base = UniqueMemberBaseName(mem);
  if (base.empty()) return;
  auto it = properties.find(base);
  if (it == properties.end()) return;
  if (!IsSolveOrderableType(it->second->data_type)) {
    diag_.Error(mem->range.start,
                "a uniqueness constraint member shall be of integral or "
                "real type");
  }
}

void ClassConstraintValidator::ValidateOneClassUniqueConstraints(
    const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& group : m->constraint_unique_refs) {
      for (const Expr* mem : group)
        ValidateOneUniqueConstraintMember(mem, properties);
    }
  }
}

void ClassConstraintValidator::ValidateUniqueConstraints() {
  for (const auto* cls : unit_->classes) ValidateOneClassUniqueConstraints(cls);
}

// 18.5.9: a variable named in a solve...before ordering shall be of integral or
// real type. Reject the types that are plainly neither — strings, events,
// chandles, virtual interfaces, void, and class handles. A typedef name is left
// alone (its underlying type is assumed orderable), keeping the check
// conservative so it never flags a legitimate integral or real variable.
bool ClassConstraintValidator::IsSolveOrderableType(const DataType& dt) const {
  switch (dt.kind) {
    case DataTypeKind::kString:
    case DataTypeKind::kEvent:
    case DataTypeKind::kChandle:
    case DataTypeKind::kVirtualInterface:
    case DataTypeKind::kVoid:
      return false;
    case DataTypeKind::kNamed:
      return FindClassDecl(dt.type_name, unit_) == nullptr;
    default:
      return true;
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
    diag.Error(loc, std::format("randc variable '{}' is not allowed in a "
                                "solve...before ordering constraint",
                                e.name));
    return nullptr;
  }
  if (!prop->is_rand) {
    diag.Error(loc, std::format("'{}' is not a random variable and cannot "
                                "appear in a solve...before ordering "
                                "constraint",
                                e.name));
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
// integral/real-type diagnostics for it. The orderability check mirrors
// ClassConstraintValidator::IsSolveOrderableType, kept here as a free helper so
// the check needs no validator instance.
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

static void CheckSolveBeforeEntry(
    const ConstraintSolveBeforeEntry& e, const SourceLoc& loc,
    const std::unordered_map<std::string_view, const ClassMember*>& properties,
    const CompilationUnit* unit, DiagEngine& diag) {
  const ClassMember* prop = ResolveSolveBeforeEntry(e, loc, properties, diag);
  if (prop && !IsSolveOrderableTypeFree(prop->data_type, unit)) {
    diag.Error(loc,
               std::format("solve...before ordering variable '{}' shall be "
                           "of integral or real type",
                           e.name));
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
                "circular dependency in solve...before variable ordering");
  }
}

void ClassConstraintValidator::ValidateSolveBeforeConstraints() {
  for (const auto* cls : unit_->classes)
    ValidateOneClassSolveBeforeConstraints(cls);
}

// 18.5.13.1: soft constraints can only be specified on random variables; they
// may not be specified for randc variables. Resolve each bare local variable
// named in a soft constraint expression against the class and its base chain
// (a derived declaration shadows a base one) and reject one that resolves to a
// randc property. As with the solve...before and foreach checks, only simple
// local identifiers the parser recorded are considered; a qualified reference
// or one that does not resolve to a local property is left alone.
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
                                ref.name));
      }
    }
  }
}

void ClassConstraintValidator::ValidateSoftConstraintVariables() {
  for (const auto* cls : unit_->classes)
    ValidateOneClassSoftConstraintVariables(cls);
}

}  // namespace delta
