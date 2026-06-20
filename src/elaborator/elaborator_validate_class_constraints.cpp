#include <algorithm>
#include <format>
#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
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

// 18.4: validate the union-rand restrictions on a single rand/randc property.
// Resolves the declared type through any typedef chain so that a union hidden
// behind a named type is still examined, then rejects the non-randomizable
// union flavors (unpacked, or packed tagged).
static void ValidateRandUnionMember(const ClassMember* m,
                                    const TypedefMap& typedefs,
                                    DiagEngine& diag) {
  // Resolve the declared type through any typedef chain so that a union
  // hidden behind a named type is still examined.
  const DataType* resolved = &m->data_type;
  for (int hops = 0; hops < 8 && resolved->kind == DataTypeKind::kNamed;
       ++hops) {
    auto it = typedefs.find(resolved->type_name);
    if (it == typedefs.end()) break;
    resolved = &it->second;
  }
  // Only a packed untagged union may be randomized: it is treated as an
  // integral value. An unpacked union has no single integral image, and a
  // packed tagged union carries a tag that randomization cannot honor.
  if (resolved->kind != DataTypeKind::kUnion) return;
  if (!resolved->is_packed) {
    diag.Error(m->loc, std::format("unpacked union '{}' shall not be declared "
                                   "rand or randc",
                                   m->name));
  } else if (resolved->is_tagged) {
    diag.Error(m->loc, std::format("packed tagged union '{}' shall not be "
                                   "declared rand or randc",
                                   m->name));
  }
}

void Elaborator::ValidateOneClassRandomVariables(const ClassDecl* cls) {
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

    if (m->is_rand || m->is_randc) ValidateRandUnionMember(m, typedefs_, diag_);
  }
}

void Elaborator::ValidateRandomVariableTypes() {
  for (const auto* cls : unit_->classes) ValidateOneClassRandomVariables(cls);
}

// 18.5: constraint block names shall be unique within a class.
void Elaborator::ValidateOneClassConstraintNames(const ClassDecl* cls) {
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

void Elaborator::ValidateConstraintBlockNames() {
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

// 18.5.7.1: a simple integral/vector type whose dimensionality is determined
// entirely by its own declaration. The loop-variable-count check is confined to
// these so that a typedef'd or aggregate element type, which may contribute
// hidden packed dimensions, is conservatively left alone.
static bool IsSimpleIntegralVectorKind(DataTypeKind k) {
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
      return true;
    default:
      return false;
  }
}

// 18.5.7.1: in a foreach iterative constraint the number of loop variables
// shall not exceed the number of dimensions of the iterated array. The array is
// a class property, possibly inherited, so resolve the name through the class
// and its base-class chain; a derived declaration shadows a base one. Only
// simple integral/vector arrays with at least one dimension are checked, which
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
  if (!IsSimpleIntegralVectorKind(it->second->data_type.kind)) return;
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

void Elaborator::ValidateOneClassForeachConstraintDims(const ClassDecl* cls) {
  auto properties = BuildClassPropertyMap(cls, unit_);

  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& fe : m->constraint_foreach_refs)
      CheckOneForeachConstraintRef(fe, properties, diag_);
  }
}

void Elaborator::ValidateForeachConstraintDims() {
  for (const auto* cls : unit_->classes)
    ValidateOneClassForeachConstraintDims(cls);
}

// 18.5.9: a variable named in a solve...before ordering shall be of integral or
// real type. Reject the types that are plainly neither — strings, events,
// chandles, virtual interfaces, void, and class handles. A typedef name is left
// alone (its underlying type is assumed orderable), keeping the check
// conservative so it never flags a legitimate integral or real variable.
bool Elaborator::IsSolveOrderableType(const DataType& dt) const {
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
// Elaborator::IsSolveOrderableType, kept here as a free helper so the per-entry
// check needs no Elaborator instance.
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

void Elaborator::ValidateOneClassSolveBeforeConstraints(const ClassDecl* cls) {
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

void Elaborator::ValidateSolveBeforeConstraints() {
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
void Elaborator::ValidateOneClassSoftConstraintVariables(const ClassDecl* cls) {
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

void Elaborator::ValidateSoftConstraintVariables() {
  for (const auto* cls : unit_->classes)
    ValidateOneClassSoftConstraintVariables(cls);
}

// 18.5.11: locate a function method of the given name visible in 'cls' or any
// of its base classes, returning its ModuleItem (the function declaration) or
// nullptr. The nearest declaration wins, matching ordinary method lookup.
static const ModuleItem* FindClassFunction(const ClassDecl* cls,
                                           std::string_view name,
                                           const CompilationUnit* unit) {
  for (const auto* c = cls; c; c = c->base_class.empty()
                                       ? nullptr
                                       : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->name == name && m->method &&
          m->method->kind == ModuleItemKind::kFunctionDecl) {
        return m->method;
      }
    }
  }
  return nullptr;
}

// 18.5.11: true when this expression node itself is a member-access call to the
// built-in rand_mode()/constraint_mode() method (independent of its operands).
static bool IsModeMethodCall(const Expr* e) {
  if (e->kind != ExprKind::kCall) return false;
  const Expr* callee = e->lhs;
  return callee && callee->kind == ExprKind::kMemberAccess && callee->rhs &&
         callee->rhs->kind == ExprKind::kIdentifier &&
         (callee->rhs->text == "rand_mode" ||
          callee->rhs->text == "constraint_mode");
}

static bool ExprCallsModeMethod(const Expr* e);

// True if any single-expression operand field of 'e' contains a
// rand_mode()/constraint_mode() call.
static bool ScalarExprFieldsCallModeMethod(const Expr* e) {
  return ExprCallsModeMethod(e->lhs) || ExprCallsModeMethod(e->rhs) ||
         ExprCallsModeMethod(e->base) || ExprCallsModeMethod(e->index) ||
         ExprCallsModeMethod(e->index_end) ||
         ExprCallsModeMethod(e->condition) ||
         ExprCallsModeMethod(e->true_expr) ||
         ExprCallsModeMethod(e->false_expr) ||
         ExprCallsModeMethod(e->repeat_count) ||
         ExprCallsModeMethod(e->with_expr);
}

// True if any element of the list-valued operand fields of 'e' (call arguments
// or aggregate elements) contains a rand_mode()/constraint_mode() call.
static bool ListExprFieldsCallModeMethod(const Expr* e) {
  for (const auto* a : e->args)
    if (ExprCallsModeMethod(a)) return true;
  for (const auto* el : e->elements)
    if (ExprCallsModeMethod(el)) return true;
  return false;
}

// Recurse into every sub-expression of 'e', returning true if any contains a
// rand_mode()/constraint_mode() call.
static bool AnyChildExprCallsModeMethod(const Expr* e) {
  return ScalarExprFieldsCallModeMethod(e) || ListExprFieldsCallModeMethod(e);
}

// 18.5.11: a function called in a constraint cannot modify the constraints, for
// example by calling rand_mode() or constraint_mode(). Search an expression for
// a member-access call to either built-in method.
static bool ExprCallsModeMethod(const Expr* e) {
  if (!e) return false;
  if (IsModeMethodCall(e)) return true;
  return AnyChildExprCallsModeMethod(e);
}

static bool StmtCallsModeMethod(const Stmt* s);

// 18.5.11: true if any expression field directly held by statement 's'
// contains a rand_mode()/constraint_mode() call (not its substatements).
static bool StmtExprFieldsCallModeMethod(const Stmt* s) {
  if (ExprCallsModeMethod(s->condition)) return true;
  if (ExprCallsModeMethod(s->lhs)) return true;
  if (ExprCallsModeMethod(s->rhs)) return true;
  if (ExprCallsModeMethod(s->for_cond)) return true;
  if (ExprCallsModeMethod(s->expr)) return true;
  if (ExprCallsModeMethod(s->var_init)) return true;
  return false;
}

// 18.5.11: true if any case or randcase arm of 's' (its guard expressions or
// its arm body) contains a rand_mode()/constraint_mode() call.
static bool CaseArmsCallModeMethod(const Stmt* s) {
  for (const auto& ci : s->case_items) {
    for (const auto* p : ci.patterns)
      if (ExprCallsModeMethod(p)) return true;
    if (StmtCallsModeMethod(ci.body)) return true;
  }
  for (const auto& [w, body] : s->randcase_items) {
    if (ExprCallsModeMethod(w)) return true;
    if (StmtCallsModeMethod(body)) return true;
  }
  return false;
}

// 18.5.11: true if any list-valued substatement field of 's' (block/fork
// bodies, for-loop inits and steps) contains a rand_mode()/constraint_mode()
// call.
static bool StmtListChildrenCallModeMethod(const Stmt* s) {
  for (const auto* sub : s->stmts)
    if (StmtCallsModeMethod(sub)) return true;
  for (const auto* sub : s->fork_stmts)
    if (StmtCallsModeMethod(sub)) return true;
  for (const auto* fi : s->for_inits)
    if (StmtCallsModeMethod(fi)) return true;
  for (const auto* fs : s->for_steps)
    if (StmtCallsModeMethod(fs)) return true;
  return false;
}

// 18.5.11: true if any single-substatement field of 's' (branch arms, loop and
// generic bodies) contains a rand_mode()/constraint_mode() call.
static bool ScalarStmtChildrenCallModeMethod(const Stmt* s) {
  return StmtCallsModeMethod(s->then_branch) ||
         StmtCallsModeMethod(s->else_branch) || StmtCallsModeMethod(s->body) ||
         StmtCallsModeMethod(s->for_body);
}

// 18.5.11: recurse into every substatement (and the expressions guarding case
// and randcase arms) of 's', returning true on a rand_mode()/constraint_mode()
// call.
static bool StmtChildrenCallModeMethod(const Stmt* s) {
  return CaseArmsCallModeMethod(s) || ScalarStmtChildrenCallModeMethod(s) ||
         StmtListChildrenCallModeMethod(s);
}

// 18.5.11: recursively search a statement (and its substatements and
// subexpressions) for a rand_mode()/constraint_mode() call.
static bool StmtCallsModeMethod(const Stmt* s) {
  if (!s) return false;
  if (StmtExprFieldsCallModeMethod(s)) return true;
  return StmtChildrenCallModeMethod(s);
}

// 18.5.11: enforce the restrictions on a function used in a constraint:
//   - It shall not have output, inout, or (non-const) ref arguments — only
//     input and const ref are permitted, so the call cannot write back into the
//     solver's variables.
//   - It cannot modify the constraints, e.g. by calling rand_mode() or
//     constraint_mode().
// The parser records every unqualified call in a constraint body; here each
// callee that resolves to a method of the enclosing class hierarchy is checked.
// A name that does not resolve to a class function (a free function or an array
// built-in such as size()) is left to other passes.
// 18.5.11: apply the function-used-in-constraint restrictions to one resolved
// callee 'fn' referenced at 'ref': no output/inout/non-const-ref arguments, and
// no body call to rand_mode()/constraint_mode().
static void ValidateConstraintCallee(const ConstraintFunctionCallRef& ref,
                                     const ModuleItem* fn, DiagEngine& diag) {
  for (const auto& arg : fn->func_args) {
    bool bad = arg.direction == Direction::kOutput ||
               arg.direction == Direction::kInout ||
               (arg.direction == Direction::kRef && !arg.is_const);
    if (bad) {
      diag.Error(
          ref.loc,
          std::format("function '{}' used in a constraint shall not have "
                      "output, inout, or non-const ref arguments",
                      ref.callee));
      break;
    }
  }
  for (const auto* s : fn->func_body_stmts) {
    if (StmtCallsModeMethod(s)) {
      diag.Error(
          ref.loc,
          std::format("function '{}' used in a constraint cannot modify the "
                      "constraints by calling rand_mode or constraint_mode",
                      ref.callee));
      break;
    }
  }
}

void Elaborator::ValidateOneClassConstraintFunctionArgs(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_function_call_refs) {
      const ModuleItem* fn = FindClassFunction(cls, ref.callee, unit_);
      if (!fn) continue;
      ValidateConstraintCallee(ref, fn, diag_);
    }
  }
}

void Elaborator::ValidateConstraintFunctionArgs() {
  for (const auto* cls : unit_->classes)
    ValidateOneClassConstraintFunctionArgs(cls);
}

// 18.8: rand_mode() is built-in and cannot be overridden. A user class
// therefore shall not declare a method named rand_mode; doing so is reported
// 18.6.2: pre_randomize() and post_randomize() are built-in methods with a
// fixed prototype, 'function void <name>();'. Unlike rand_mode and
// constraint_mode a user may override them, but an override shall match that
// prototype: a void-returning function taking no arguments. A task form, a
// non-void return type, or any formal argument does not conform.
static void ValidatePrePostRandomizePrototype(const ClassMember* m,
                                              DiagEngine& diag) {
  const ModuleItem* fn = m->method;
  if (!fn) return;
  if (fn->kind != ModuleItemKind::kFunctionDecl) {
    diag.Error(m->loc, std::format("'{}' shall be a void function taking no "
                                   "arguments, not a task",
                                   m->name));
    return;
  }
  if (fn->return_type.kind != DataTypeKind::kVoid) {
    diag.Error(m->loc,
               std::format("'{}' shall have a void return type", m->name));
  }
  if (!fn->func_args.empty()) {
    diag.Error(m->loc, std::format("'{}' shall take no arguments", m->name));
  }
}

// as an error rather than silently shadowing the built-in method.
void Elaborator::ValidateOneClassBuiltinMethods(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod) continue;
    if (m->name == "rand_mode") {
      diag_.Error(m->loc,
                  "'rand_mode' is a built-in method and cannot be overridden");
    }
    // 18.9: constraint_mode() is likewise a built-in method that a class may
    // not redefine.
    if (m->name == "constraint_mode") {
      diag_.Error(
          m->loc,
          "'constraint_mode' is a built-in method and cannot be overridden");
    }
    // 18.6.3: randomize() is a built-in method and cannot be overridden, so a
    // user class shall not declare a method named randomize. (pre_randomize and
    // post_randomize are different: 18.6.2 permits overriding those, subject to
    // the prototype check below.)
    if (m->name == "randomize") {
      diag_.Error(m->loc,
                  "'randomize' is a built-in method and cannot be overridden");
    }
    if (m->name == "pre_randomize" || m->name == "post_randomize") {
      ValidatePrePostRandomizePrototype(m, diag_);
    }
  }
}

void Elaborator::ValidateBuiltinRandomizationMethods() {
  for (const auto* cls : unit_->classes) ValidateOneClassBuiltinMethods(cls);
}

// True when location 'a' lies strictly before location 'b' within one file.
// Locations in different files are treated as unordered (returns false).
static bool LocStrictlyBefore(const SourceLoc& a, const SourceLoc& b) {
  if (a.file_id != b.file_id) return false;
  if (a.line != b.line) return a.line < b.line;
  return a.column < b.column;
}

// 18.5.1: an external constraint block completes a constraint prototype.
//   - The explicit prototype form ('extern constraint name;') shall have a
//     corresponding external constraint block.
//   - An implicit prototype ('constraint name;') with no external block is
//     treated as an empty constraint (no effect on randomization); this is
//     legal.
//   - No prototype may be completed by more than one external block.
// 18.5.1: validate one constraint prototype against the external constraint
// blocks: an explicit prototype with no block is an error, and a prototype
// completed by more than one block is an error.
static void ValidateOnePrototypeCompletion(
    const ClassMember* m, std::string_view cls_name,
    const std::vector<ExternalConstraintBlock>& exts, DiagEngine& diag) {
  int matches = 0;
  for (const auto& ext : exts) {
    if (ext.class_name == cls_name && ext.constraint_name == m->name) {
      ++matches;
    }
  }

  if (matches == 0) {
    if (m->is_constraint_extern) {
      diag.Error(m->loc,
                 std::format("explicit constraint prototype '{}' in class "
                             "'{}' has no external constraint block",
                             m->name, cls_name));
    }
    // Implicit prototype with no external block: empty constraint, legal.
  } else if (matches > 1) {
    diag.Error(m->loc,
               std::format("constraint prototype '{}' in class '{}' is "
                           "completed by more than one external constraint "
                           "block",
                           m->name, cls_name));
  }
}

void Elaborator::ValidateOneClassExternalConstraints(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (!m->is_constraint_prototype) continue;
    // Pure constraints are obligations governed by 18.5.2, not completed by an
    // external block, so they are outside the scope of this check.
    if (m->is_pure_virtual) continue;
    ValidateOnePrototypeCompletion(m, cls->name, unit_->external_constraints,
                                   diag_);
  }
}

// 18.5.2: walks the superclass chain looking for a constraint of the given
// name. Returns the nearest such constraint member, or nullptr when no base
// class declares one. A derived constraint of the same name replaces it.
static const ClassMember* FindBaseConstraint(const ClassDecl* cls,
                                             std::string_view name,
                                             const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == name) {
        return m;
      }
    }
  }
  return nullptr;
}

// 18.5.2: like FindBaseConstraint but only reports a same-named base
// constraint that was declared with the 'final' specifier, which a subclass
// is forbidden from replacing.
static const ClassMember* FindBaseFinalConstraint(const ClassDecl* cls,
                                                  std::string_view name,
                                                  const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindClassDecl(cls->base_class, unit); c;
       c = c->base_class.empty() ? nullptr
                                 : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == name &&
          m->is_constraint_final) {
        return m;
      }
    }
  }
  return nullptr;
}

// 18.5.2: enforces the dynamic override specifiers on a single constraint.
//   - ':initial' declares the constraint is not an override, so a same-named
//     base constraint is an error.
//   - ':extends' declares the constraint is an override, so the absence of a
//     same-named base constraint is an error.
//   - ':initial' and ':extends' are mutually exclusive.
//   - Replacing a base constraint declared ':final' is an error.
void Elaborator::ValidateOneConstraintOverride(const ClassDecl* cls,
                                               const ClassMember* m) {
  if (m->is_constraint_initial && m->is_constraint_extends) {
    diag_.Error(m->loc,
                std::format("constraint '{}' shall not specify both ':initial' "
                            "and ':extends'",
                            m->name));
  }

  // 18.5.10: it is illegal to use the dynamic override specifiers ':initial',
  // ':extends', or ':final' on a constraint that is qualified 'static'.
  if (m->is_static && (m->is_constraint_initial || m->is_constraint_extends ||
                       m->is_constraint_final)) {
    diag_.Error(m->loc,
                std::format("static constraint '{}' shall not carry a dynamic "
                            "override specifier",
                            m->name));
  }

  const auto* base = FindBaseConstraint(cls, m->name, unit_);

  // 18.5.10: a pure constraint may be qualified 'static', and an overriding
  // constraint shall match that qualification — static if the pure constraint
  // is static, non-static if it is not.
  if (base != nullptr && base->is_pure_virtual && !m->is_pure_virtual &&
      m->is_static != base->is_static) {
    diag_.Error(
        m->loc,
        std::format("constraint '{}' overriding a pure constraint shall "
                    "match its 'static' qualification",
                    m->name));
  }

  if (m->is_constraint_initial && base) {
    diag_.Error(m->loc,
                std::format("constraint '{}' declared ':initial' overrides a "
                            "constraint of the same name in a base class",
                            m->name));
  }
  if (m->is_constraint_extends && !base) {
    diag_.Error(m->loc,
                std::format("constraint '{}' declared ':extends' does not "
                            "override a constraint in a base class",
                            m->name));
  }

  if (base != nullptr && FindBaseFinalConstraint(cls, m->name, unit_)) {
    diag_.Error(m->loc,
                std::format("constraint '{}' replaces a base class constraint "
                            "declared ':final'",
                            m->name));
  }
}

// 18.5.2: gathers the names of pure constraints inherited by 'cls' that no
// class on the path down to 'cls' has overridden with a non-pure constraint.
static void CollectInheritedPureConstraints(
    const ClassDecl* cls, const CompilationUnit* unit,
    std::vector<std::string_view>& pure_names) {
  if (!cls) return;
  if (!cls->base_class.empty()) {
    CollectInheritedPureConstraints(FindClassDecl(cls->base_class, unit), unit,
                                    pure_names);
  }
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (m->is_pure_virtual) {
      pure_names.push_back(m->name);
    } else {
      // A non-pure constraint of the same name overrides the obligation.
      std::erase(pure_names, m->name);
    }
  }
}

// 18.5.2: a non-abstract class shall provide an implementation for every pure
// constraint it inherits, and a pure constraint shall not be declared in a
// non-abstract class.
void Elaborator::ValidateNonAbstractPureConstraints(const ClassDecl* cls) {
  if (cls->is_virtual) return;

  std::vector<std::string_view> unimpl;
  if (!cls->base_class.empty()) {
    CollectInheritedPureConstraints(FindClassDecl(cls->base_class, unit_),
                                    unit_, unimpl);
  }
  // Constraints declared in this class override any inherited obligation of
  // the same name; only a same-named non-pure constraint discharges it.
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && !m->is_pure_virtual) {
      std::erase(unimpl, m->name);
    }
  }
  for (auto name : unimpl) {
    diag_.Error(cls->range.start,
                std::format("non-abstract class '{}' does not implement "
                            "inherited pure constraint '{}'",
                            cls->name, name));
  }
}

// 18.5.2: a constraint completed by a prototype plus an external constraint
// block shall carry the same dynamic override specifiers on both the prototype
// and the external block, or on neither.
void Elaborator::ValidateConstraintSpecifierParity(const ClassDecl* cls,
                                                   const ClassMember* m) {
  for (const auto& ext : unit_->external_constraints) {
    if (ext.class_name != cls->name || ext.constraint_name != m->name) continue;
    if (m->is_constraint_initial != ext.is_initial ||
        m->is_constraint_extends != ext.is_extends ||
        m->is_constraint_final != ext.is_final) {
      diag_.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' and its prototype "
                      "disagree on dynamic override specifiers",
                      cls->name, m->name));
    }
    // 18.5.10: the 'static' keyword shall be applied to both the constraint
    // prototype and the external constraint block, or to neither.
    if (m->is_static != ext.is_static) {
      diag_.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' and its prototype "
                      "disagree on the 'static' qualifier",
                      cls->name, m->name));
    }
  }
}

// 18.5.2: a class that declares a pure constraint shall not also complete a
// constraint of the same name with an external constraint block, nor declare a
// same-name non-pure constraint block or constraint prototype in the same class
// body.
static void ValidatePureConstraintConflicts(const ClassDecl* cls,
                                            const ClassMember* m,
                                            const CompilationUnit* unit,
                                            DiagEngine& diag) {
  for (const auto& ext : unit->external_constraints) {
    if (ext.class_name == cls->name && ext.constraint_name == m->name) {
      diag.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' conflicts with "
                      "a pure constraint of the same name",
                      cls->name, m->name));
      break;
    }
  }
  for (const auto* other : cls->members) {
    if (other == m) continue;
    if (other->kind != ClassMemberKind::kConstraint) continue;
    if (other->name != m->name) continue;
    if (other->is_pure_virtual) continue;
    diag.Error(other->loc,
               std::format("constraint '{}' in class '{}' conflicts "
                           "with a pure constraint of the same name",
                           other->name, cls->name));
  }
}

void Elaborator::ValidateConstraintInheritance() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kConstraint) continue;
      // 18.5.2: a pure constraint is an obligation and may only appear in an
      // abstract (virtual) class.
      if (m->is_pure_virtual && !cls->is_virtual) {
        diag_.Error(m->loc,
                    std::format("pure constraint '{}' shall not be declared in "
                                "non-abstract class '{}'",
                                m->name, cls->name));
      }
      if (m->is_pure_virtual) {
        ValidatePureConstraintConflicts(cls, m, unit_, diag_);
      } else if (m->is_constraint_prototype) {
        ValidateConstraintSpecifierParity(cls, m);
      }
      ValidateOneConstraintOverride(cls, m);
    }
    ValidateNonAbstractPureConstraints(cls);
  }
}

void Elaborator::ValidateExternalConstraints() {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassExternalConstraints(cls);
  }

  // 18.5.1: an external constraint block shall appear in the same scope as its
  // class declaration and after that class declaration. The block and the
  // top-level class share a scope here; flag a block that precedes the end of
  // its class declaration.
  for (const auto& ext : unit_->external_constraints) {
    const ClassDecl* target = nullptr;
    for (const auto* cls : unit_->classes) {
      if (cls->name == ext.class_name) {
        target = cls;
        break;
      }
    }
    if (target == nullptr) continue;
    if (!LocStrictlyBefore(target->range.end, ext.loc)) {
      diag_.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' shall appear "
                      "after the declaration of class '{}'",
                      ext.class_name, ext.constraint_name, ext.class_name));
    }
  }
}

}  // namespace delta
