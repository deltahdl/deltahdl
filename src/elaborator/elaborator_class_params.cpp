#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// §8.23: a class value parameter or local parameter is a public element and a
// constant expression, reachable from outside the class via the class scope
// resolution operator (Class::PARAM). Record each such parameter under its
// "Class.name" key so a constant expression referring to it -- which parses as
// a member access whose compound key is "Class.name" -- folds at elaboration.
// Type parameters carry no value and are skipped.
//
// A value that is not a constant expression is reported here rather than left
// out. §6.20.1's Syntax 6-6 writes a param_assignment as `parameter_identifier
// { variable_dimension } [ = constant_param_expression ]`, and makes every
// param_assignment in a class body a localparam declaration whether or not the
// class has a parameter_port_list (printed page 125 of IEEE 1800-2023),
// so a class body parameter and a #() parameter port are both under that rule.
// Leaving the parameter out instead is what let a breach elaborate in silence:
// a name absent from the scope reads to every later consumer as a name it
// cannot see rather than as a value the source got wrong, and
// CollectUnpackedDimSizes in elaborator_decls_var.cpp drops the array dimension
// the parameter was sizing rather than reporting it.
//
// §6.20.1: one class's list of parameter constants, as far as registration has
// read it. `formals` holds every parameter name the class declares, type
// parameters included; a value that mentions one is left alone whether it folds
// or not, because §8.25 binds those only when the class is specialized, and
// `class C #(type T = int, int S = $bits(T));` is legal and has no value where
// it stands. `values` is `cu_param_scope` with the values recorded so far
// layered over it under their bare names, which is what §6.20.1 requires when
// it lets a parameter in a list of parameter constants depend on earlier ones.
// The three fields that follow are where a recorded value goes and how a
// breach is reported.
struct ClassParamRegistration {
  const ClassDecl* cls;
  std::unordered_set<std::string_view> formals;
  ScopeMap values;
  ScopeMap& cu_param_scope;
  Arena& arena;
  DiagEngine& diag;
};

// §6.20.7 (printed page 131): `$` assigned to a parameter, which stands for no
// number and so has none to fold.
static bool IsDollarValue(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

// §6.20.2 (printed pages 126-127): whether a class value parameter declared
// with `type` takes a real value -- declared with a real type, or declared
// with neither type nor range and given a real expression, where "if the
// expression is real, the parameter is real". Null for a declaration
// recording no type.
static bool TakesRealClassParamValue(const Expr* pexpr, const DataType* type) {
  if (type != nullptr && IsRealType(type->kind)) return true;
  bool untyped =
      type == nullptr || (type->kind == DataTypeKind::kImplicit &&
                          !type->is_signed && type->packed_dim_left == nullptr);
  return untyped && HasRealOperand(pexpr);
}

// §8.25 with §6.20.2 (printed pages 126-127) and §11.6.1: an integral value is
// folded as the right-hand side of an assignment to a parameter of the
// declared `type`, its range folded against the parameters recorded before it
// (FoldDeclaredParamValue), so `logic [W-1:0] INIT = '1` after `int W = 8`
// records 255 and not the 1 the literal is on its own (§5.7.1). §6.20.2 also
// applies §6.12.1's conversion to parameters, so a real expression given to a
// parameter of an integral type is rounded (FoldRealValueAsInteger), ahead of
// the integer fold as a module's parameter orders the two.
static std::optional<int64_t> FoldClassParamInteger(const Expr* pexpr,
                                                    const DataType* type,
                                                    const ScopeMap& values) {
  if (type == nullptr) return ConstEvalInt(pexpr, values);
  if (auto rounded = FoldRealValueAsInteger(pexpr, values)) return rounded;
  return FoldDeclaredParamValue(pexpr, *type, values);
}

// A real value and `$` are checked for being constant and recorded nowhere,
// since the qualified "Class.name" scope holds integers alone; the simulator
// reads a real class parameter as a real (ClassParamSizer in
// src/simulator/eval_class_params.cpp).
static void RecordClassParam(std::string_view pname, const Expr* pexpr,
                             const DataType* type,
                             ClassParamRegistration& reg) {
  if (!pexpr || IsDollarValue(pexpr)) return;
  bool is_real = TakesRealClassParamValue(pexpr, type);
  std::optional<int64_t> val;
  if (!is_real) val = FoldClassParamInteger(pexpr, type, reg.values);
  if (is_real ? !ConstEvalReal(pexpr, reg.values) : !val) {
    if (!ExprMentionsAny(pexpr, reg.formals)) {
      reg.diag.Error(pexpr->range.start,
                     std::format("class parameter '{}' value is not a constant "
                                 "expression",
                                 pname),
                     Subclause("6.20.2"));
    }
    return;
  }
  if (is_real) return;
  auto* qname = reg.arena.Create<std::string>(std::string(reg.cls->name) + "." +
                                              std::string(pname));
  reg.cu_param_scope[*qname] = *val;
  reg.values[pname] = *val;
}

// The #() parameter ports live in cls->params; type parameters carry no value
// and are skipped. They are taken before the body declarations because that is
// the order they are written in, and a body declaration may name one of them.
// Body parameter and localparam declarations are class members flagged is_param
// (parser_class.cpp records them as kProperty members).
static void RegisterOneClassParams(ClassParamRegistration& reg) {
  const auto& params = reg.cls->params;
  const auto& types = reg.cls->param_types;
  for (size_t i = 0; i < params.size(); ++i) {
    const auto& [pname, pexpr] = params[i];
    if (reg.cls->type_param_names.count(pname)) continue;
    RecordClassParam(pname, pexpr, i < types.size() ? &types[i] : nullptr, reg);
  }
  for (const auto* m : reg.cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param)
      RecordClassParam(m->name, m->init_expr, &m->data_type, reg);
  }
}

void RegisterClassParams(CompilationUnit* unit, ScopeMap& cu_param_scope,
                         Arena& arena, DiagEngine& diag) {
  for (auto* cls : unit->classes) {
    // cu_param_scope appears twice: once copied into `values`, which the class
    // layers its own bare names over, and once bound as the scope the qualified
    // "Class.name" keys are written to.
    ClassParamRegistration reg{
        cls, ClassParamNames(cls), cu_param_scope, cu_param_scope, arena, diag};
    RegisterOneClassParams(reg);
  }
}

// §8.26: "A class declaration may appear ... within a module", and §6.20.1 says
// the same thing of every class body wherever it stands: "All param_assignments
// appearing within a class body shall become localparam declarations regardless
// of the presence or absence of a parameter_port_list", whose value Syntax 6-6
// makes a constant_param_expression. The walk below reaches the compilation
// unit's classes alone, so a class written inside a module had its defaults
// folded and checked nowhere and `class C #(parameter int W = n);` over a
// variable n elaborated in silence -- and the default was then evaluated at
// each construction against the simulation context, a per-object value where
// §6.20 has one constant.
//
// `module_scope` is what the class layers its own names over, so a default
// naming one of the module's parameters folds against it, and the qualified
// "Class.name" keys go to the compilation-unit scope the unit's classes write
// to, which is where every consumer of a class parameter looks.
void RegisterModuleClassParams(const ClassDecl* cls,
                               const ScopeMap& module_scope,
                               ScopeMap& cu_param_scope, Arena& arena,
                               DiagEngine& diag) {
  ClassParamRegistration reg{
      cls, ClassParamNames(cls), module_scope, cu_param_scope, arena, diag};
  RegisterOneClassParams(reg);
}

// Whether `e` mentions any name in `names`, at any depth. Every identifier the
// expression carries is compared, whatever node holds it, so a type parameter
// named by a `type` operator or a cast counts as a mention.
bool ExprMentionsAny(const Expr* e,
                     const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (!e->text.empty() && names.count(e->text)) return true;
  if (!e->callee.empty() && names.count(e->callee)) return true;
  for (const Expr* child :
       {e->lhs, e->rhs, e->condition, e->true_expr, e->false_expr, e->base,
        e->index, e->index_end, e->with_expr}) {
    if (ExprMentionsAny(child, names)) return true;
  }
  for (const Expr* arg : e->args) {
    if (ExprMentionsAny(arg, names)) return true;
  }
  for (const Expr* elem : e->elements) {
    if (ExprMentionsAny(elem, names)) return true;
  }
  return false;
}

// §6.20.7 (printed page 131): a parameter holding `$` may stand wherever `$`
// may be written as a literal, which an override is. Its value is not in the
// ScopeMap, so it is found among the parameters of the module a live
// ParamRangeRegistryGuard registered.
static bool NamesUnboundedParam(const Expr* e) {
  if (e->kind != ExprKind::kIdentifier) return false;
  const RtlirParamDecl* pd = RegisteredParamNamed(e->text);
  return pd != nullptr && pd->is_unbounded;
}

std::unordered_set<std::string_view> NonIntegralParamNames(
    const std::vector<ModuleItem*>* items, const ScopeMap& values) {
  std::unordered_set<std::string_view> names;
  if (items == nullptr) return names;
  for (const auto* item : *items) {
    if (item == nullptr || item->kind != ModuleItemKind::kParamDecl) continue;
    const Expr* v = item->init_expr;
    if (v == nullptr) continue;
    bool names_one = v->kind == ExprKind::kIdentifier && names.count(v->text);
    bool is_real = HasRealOperand(v) && ConstEvalReal(v, values);
    if (IsDollarValue(v) || names_one || is_real) names.insert(item->name);
  }
  return names;
}

bool IsConstantClassParamValue(const Expr* e, const ScopeMap& scope) {
  return IsDollarValue(e) || NamesUnboundedParam(e) || ConstEvalInt(e, scope) ||
         ConstEvalReal(e, scope);
}

// Every parameter name `cls` declares: its type parameters, its #() parameter
// ports and its body parameter declarations.
std::unordered_set<std::string_view> ClassParamNames(const ClassDecl* cls) {
  std::unordered_set<std::string_view> names = cls->type_param_names;
  for (const auto& [pname, pexpr] : cls->params) names.insert(pname);
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param)
      names.insert(m->name);
  }
  return names;
}

}  // namespace delta
