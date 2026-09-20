#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// §6.20.2 (printed page 127) with §6.12.1: the value of an integer parameter
// whose value expression `expr` is real -- has a real literal, a time literal
// or a call of one of §20.5's real-returning conversions as an operand --
// folded against `scope` and rounded to the nearest integer, ties away from
// zero. Empty for an expression with no real operand, whatever the integer
// fold made of it, and for a real value that is not a number, which §11.4.3
// (printed 276) leaves unspecified for a zero base raised to a negative
// power. Defined in elaborator_items_params.cpp, and read there by a
// parameter declared among a module's items and in
// elaborator_module_params.cpp by a parameter port.
std::optional<int64_t> FoldRealValueAsInteger(const Expr* expr,
                                              const ScopeMap& scope);

// §23.10.2 (printed page 766) and §33.4.3: the parameter value assignments of
// the instantiation being elaborated, and the scope their expressions were
// written in -- the instantiating module's parameters, which
// RegisteredModuleScope() answers while that module's items are elaborated
// and which nothing answers once the instantiated module's own are, so the
// scope is taken before they are.
struct InstanceParamAssignments {
  const Elaborator::ParamList& params;
  ScopeMap scope;
};

// Gives `pd`, the parameter named `pname` declared with the type `dtype` (null
// for one declared without), the value the assignment in `assigns` names for
// it, converted to the declared range (§6.20.2, printed page 126), with its
// words above bit 63 and its own width where the declaration fixes none
// (RecordResolvedHighWords) and the characters of a string value (§6.16, from
// `arena`). Answers whether an assignment named the parameter at all. Defined
// in elaborator_module_params.cpp; Elaborator::ElaborateParamPortList calls it
// for a parameter port and Elaborator::ElaborateParamDecl for a parameter
// declared among the items of a module without a parameter port list.
bool ApplyParamOverride(RtlirParamDecl& pd,
                        const InstanceParamAssignments& assigns,
                        std::string_view pname, const DataType* dtype,
                        Arena& arena);

// §23.10 (printed page 763) with §6.20.1 (printed 125): a module declared
// with no parameter port list declares its value parameters among its items,
// and an instance's parameter value assignment overrides them there as it
// does a parameter port. Elaborator::ElaborateModule installs the
// instantiation's assignments for the duration of the module's items, and
// Elaborator::ElaborateParamDecl reads them back through
// BodyParamAssignments(): null while a module with a parameter port list is
// elaborated, whose body parameters §6.20.1 makes local parameters, and
// outside every module. An instance among the items installs its own for the
// module it instantiates and puts this one back when it returns. The pointer
// is borrowed and must outlive the guard.
class BodyParamAssignmentsGuard {
 public:
  explicit BodyParamAssignmentsGuard(const InstanceParamAssignments* assigns);
  ~BodyParamAssignmentsGuard();
  BodyParamAssignmentsGuard(const BodyParamAssignmentsGuard&) = delete;
  BodyParamAssignmentsGuard& operator=(const BodyParamAssignmentsGuard&) =
      delete;

 private:
  const InstanceParamAssignments* prev_;
};

// The assignments the innermost live BodyParamAssignmentsGuard installed, or
// null. Defined in elaborator_module_params.cpp.
const InstanceParamAssignments* BodyParamAssignments();

// §23.10.2.1 (printed page 766) with §23.10 (printed 763): the parameters of
// `decl` an instance's parameter value assignment may name, in the order an
// ordered assignment binds to them -- the parameter port list's, less the
// local parameters §6.20.4 (printed 128) puts beyond any assignment, and, for
// a module declared with no parameter port list, each `parameter` written
// among its items, in declaration order, since §6.20.1 (printed 125-126)
// makes such a parameter a value parameter and makes the same declaration a
// localparam where a parameter port list, even an empty one, is present. A
// parameter a named block, a task or a function declares is none of these
// (§23.10.2). Defined in elaborator_module_params.cpp for the instantiation
// site's ResolveInstParams to read the override surface from.
std::vector<std::string_view> OverridableParamNames(const ModuleDecl* decl);

}  // namespace delta
