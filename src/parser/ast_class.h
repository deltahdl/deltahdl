#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

enum class ClassMemberKind : uint8_t {
  kProperty,
  kMethod,
  kConstraint,
  kTypedef,
  kClassDecl,
  kCovergroup,
};

// 18.5.7.1: a foreach iterative constraint as seen in a constraint block body.
// array_name is the (trailing) identifier of the iterated array; loop_var_count
// is the number of loop variables given, counted up to the last nonempty slot
// so a trailing run of omittable commas does not inflate it. loc points at the
// foreach for diagnostics. The parser records these from the constraint body so
// the elaborator — which can resolve the array's declaration and therefore its
// dimensionality — can enforce that the loop-variable count does not exceed the
// array's number of dimensions.
struct ConstraintForeachRef {
  std::string_view array_name;
  int loop_var_count = 0;
  SourceLoc loc;
};

// 18.5.9: one constraint_primary appearing in a solve...before list. 'name' is
// the trailing (leaf) identifier of the reference. is_simple marks a bare local
// identifier — no class_scope/implicit_class_handle qualifier and no trailing
// '()' array-method call (such as size()). The elaborator only applies the
// solve...before variable restrictions (must be rand, not randc, integral or
// real) to simple entries it can resolve to a class property; a qualified or
// array-method primary is left alone, since array.size() is expressly allowed
// as an ordering variable.
struct ConstraintSolveBeforeEntry {
  std::string_view name;
  bool is_simple = true;
};

// 18.5.9: a 'solve solve_before_list before solve_before_list ;' ordering
// constraint as seen in a constraint block body. 'before' holds the variables
// to be solved first; 'after' holds those solved afterward. loc points at the
// solve keyword for diagnostics. The parser records these so the elaborator can
// enforce the variable-ordering restrictions and reject circular dependencies.
struct ConstraintSolveBeforeRef {
  std::vector<ConstraintSolveBeforeEntry> before;
  std::vector<ConstraintSolveBeforeEntry> after;
  SourceLoc loc;
};

// 18.5.11: a function call appearing in a constraint block body. 'callee' is
// the leaf identifier named immediately before the '(' (the function name); loc
// points at that name for diagnostics. Only an unqualified call is recorded —
// one not preceded by a '.' or '::' member/scope qualifier — so the elaborator
// resolves it against the enclosing class hierarchy and applies the
// restrictions on functions used in constraints (no output/inout/non-const-ref
// arguments).
struct ConstraintFunctionCallRef {
  std::string_view callee;
  SourceLoc loc;
};

// 18.5.13.1: a bare local variable named within a soft constraint expression.
// 'name' is the identifier and 'loc' points at it for diagnostics. The parser
// records only simple local references — an identifier that is neither the leaf
// of a '.'/'::' qualified reference nor a function call — so the elaborator can
// resolve each against the class and reject a soft constraint specified on a
// randc variable, which the clause forbids.
struct ConstraintSoftVarRef {
  std::string_view name;
  SourceLoc loc;
};

// 18.5.3: one dist_item of a captured distribution set. A plain item weights
// the single 'value'; is_range weights the inclusive range [lo:hi]; is_default
// marks the 'default :/ weight' item that stands for every domain value not
// named by another item. 'weight' is the dist_weight expression, left null when
// omitted (an absent weight means 1). per_element records that a range used the
// ':=' operator — the weight is applied to each element of the range — as
// opposed to
// ':/' (or a single value), which applies the weight to the item as a whole; a
// range with no explicit weight defaults to ':= 1', hence per_element.
struct ConstraintDistItem {
  Expr* value = nullptr;
  Expr* lo = nullptr;
  Expr* hi = nullptr;
  Expr* weight = nullptr;
  bool is_range = false;
  bool per_element = false;
  bool is_default = false;
};

// 18.5.3: a captured 'expression dist { dist_list }' constraint. 'target' is
// the left-hand expression whose value the distribution weights; 'items' holds
// the dist_list in source order. The parser records these so the simulator can
// build a weighted-value solver constraint for a runtime randomize() call.
struct ConstraintDistRef {
  Expr* target = nullptr;
  std::vector<ConstraintDistItem> items;
};

struct ClassMember {
  ClassMemberKind kind = ClassMemberKind::kProperty;
  SourceLoc loc;

  bool is_static = false;
  bool is_virtual = false;
  bool is_local = false;
  bool is_protected = false;
  bool is_rand = false;
  bool is_randc = false;
  bool is_const = false;
  bool is_pure_virtual = false;
  // §6.20/§8.25: this member is a parameter or localparam declaration (carried
  // with kind kProperty). Distinguished from a data property so that, e.g.,
  // §8.26 interface-class validation does not flag a parameter as a data
  // member.
  bool is_param = false;

  bool is_constraint_initial = false;
  bool is_constraint_extends = false;
  bool is_constraint_final = false;

  // 18.5.1: a constraint declared without a body is a constraint prototype that
  // is completed by an external constraint block. The explicit prototype form
  // uses the 'extern' keyword; the implicit form omits it.
  bool is_constraint_prototype = false;
  bool is_constraint_extern = false;

  // 18.5.7.1: the foreach iterative constraints found in this constraint
  // block's body (empty for non-constraint members).
  std::vector<ConstraintForeachRef> constraint_foreach_refs;

  // 18.5.9: the solve...before ordering constraints found in this constraint
  // block's body (empty for non-constraint members).
  std::vector<ConstraintSolveBeforeRef> constraint_solve_before_refs;

  // 18.5.11: the function calls found in this constraint block's body (empty
  // for non-constraint members), recorded so the elaborator can resolve each
  // callee and apply the restrictions on functions used in constraints.
  std::vector<ConstraintFunctionCallRef> constraint_function_call_refs;

  // 18.5.13.1: the bare local variables named within soft constraint
  // expressions in this constraint block's body (empty for non-constraint
  // members), recorded so the elaborator can reject a soft constraint specified
  // on a randc variable.
  std::vector<ConstraintSoftVarRef> constraint_soft_refs;

  // 18.5: the top-level constraint relation expressions of this constraint
  // block, in source order (empty for non-constraint members). The parser
  // captures these so the simulator can translate them into the constraint
  // solver's inputs for a runtime randomize() call.
  std::vector<Expr*> constraint_exprs;

  // 18.5.3: the 'expression dist { dist_list }' distributions found in this
  // constraint block's body (empty for non-constraint members). The parser
  // captures each so the simulator can build a weighted-value distribution
  // constraint for the solver.
  std::vector<ConstraintDistRef> constraint_dist_refs;

  // 18.5.13: the inner relation of each 'soft' constraint in this block's body,
  // in source order (empty for non-constraint members). A soft constraint is an
  // expression_or_dist preceded by 'soft'; its inner relation is captured apart
  // from constraint_exprs so the simulator builds it as a discardable (soft)
  // solver constraint rather than a hard one. Without this the relation would
  // be dropped and the soft preference lost entirely.
  std::vector<Expr*> constraint_soft_exprs;

  // 18.5.13: the 'soft'-prefixed distributions of this block's body, i.e. the
  // dist alternative of the soft operand's expression_or_dist. Captured apart
  // from constraint_dist_refs (which are hard) so the simulator builds each as
  // a discardable soft distribution rather than a hard one.
  std::vector<ConstraintDistRef> constraint_soft_dist_refs;

  // 18.5.4: the uniqueness constraints ("unique { range_list }") found in this
  // block's body (empty for non-constraint members). Each entry holds one
  // constraint's range_list member expressions in source order. The parser
  // captures each group so the simulator can build a kUnique solver constraint
  // for a runtime randomize() call and the elaborator can check the restricted
  // range_list member forms this subclause requires.
  std::vector<std::vector<Expr*>> constraint_unique_refs;

  DataType data_type;
  std::string_view name;
  std::vector<Expr*> unpacked_dims;
  Expr* init_expr = nullptr;

  ModuleItem* method = nullptr;
  ModuleItem* typedef_item = nullptr;

  ClassDecl* nested_class = nullptr;

  // §19.4.1: when this member is a derived covergroup declared with the
  // embedded inheritance form `covergroup extends base ;`, the
  // covergroup_identifier of the base covergroup. Empty otherwise.
  std::string_view covergroup_extends_base;
};

struct InterfaceRef {
  std::string_view name;
  std::vector<DataType> type_params;
};

struct ClassDecl {
  std::string_view name;
  SourceRange range;
  bool is_virtual = false;
  bool is_final = false;
  bool is_interface = false;
  std::string_view base_class;
  std::vector<DataType> base_class_type_params;
  std::vector<Expr*> extends_args;
  bool extends_has_default = false;
  std::vector<InterfaceRef> extends_interfaces;
  std::vector<InterfaceRef> implements_types;
  std::vector<ClassMember*> members;
  std::vector<std::pair<std::string_view, Expr*>> params;
  std::unordered_set<std::string_view> type_param_names;
  std::unordered_set<std::string_view> localparam_port_names;
};

}  // namespace delta
