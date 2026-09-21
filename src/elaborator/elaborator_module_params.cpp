// The parameters of a module's parameter port list (§6.20.1, §23.2.3) and the
// value an instance's parameter value assignment (§23.10.2) or a
// configuration's (§33.4.3) gives a parameter, moved out of
// src/elaborator/elaborator_module.cpp, which holds the module's frame, at its
// size limit.

#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

const Elaborator::ParamOverride* FindParamOverride(
    const Elaborator::ParamList& params, std::string_view name) {
  for (const auto& ovr : params) {
    if (ovr.name == name) {
      return &ovr;
    }
  }
  return nullptr;
}

// §6.20.3: follow typedef and type-parameter substitutions to decide whether a
// declared type ultimately names a class type.
static bool ParamTypeResolvesToClass(
    const DataType& dtype, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  const DataType* cur = &dtype;
  for (int depth = 0; depth < 32 && cur->kind == DataTypeKind::kNamed;
       ++depth) {
    if (class_names.count(cur->type_name) > 0) return true;
    auto it = typedefs.find(cur->type_name);
    if (it == typedefs.end()) break;
    cur = &it->second;
  }
  return false;
}

// The elaborator state needed to validate a type-parameter-typed value
// parameter's assigned value, bundled to stay within the argument-count limit.
struct TypeParamValueCtx {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
  DiagEngine& diag;
};

// §23.10.3: a value parameter whose declared type is one of this module's type
// parameters, and which (after the instance override or default) resolved to a
// class type, cannot be assigned an integral constant value. §23.10.3 states
// the rule on this very construct -- "if the type parameter T is not overridden
// to an integral type, the evaluation of the default value for parameter p is
// illegal" -- while §6.20.2 states only general assignment compatibility.
static void CheckTypeParamValueAssignable(const ModuleDecl* decl, size_t i,
                                          const Expr* pval,
                                          const ScopeMap& scope,
                                          const TypeParamValueCtx& ctx) {
  if (i >= decl->param_types.size()) return;
  const DataType& dt = decl->param_types[i];
  if (dt.kind != DataTypeKind::kNamed) return;
  if (decl->type_param_names.count(dt.type_name) == 0) return;
  if (!pval || !ConstEvalInt(pval, scope)) return;
  if (!ParamTypeResolvesToClass(dt, ctx.typedefs, ctx.class_names)) return;
  ctx.diag.Error(pval->range.start,
                 std::format("cannot assign an integral value to parameter "
                             "whose type parameter '{}' resolved to a class "
                             "type",
                             dt.type_name),
                 Subclause("23.10.3"));
}

bool Elaborator::HasParamPortWithoutDefault(const ModuleDecl* decl) {
  for (const auto& [name, expr] : decl->params) {
    if (decl->localparam_port_names.count(name)) continue;
    if (decl->type_param_names.count(name)) continue;
    if (expr == nullptr) return true;
  }
  return false;
}

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype) {
  pd.has_decl_range = dtype.packed_dim_left != nullptr;
  pd.has_decl_type = dtype.kind != DataTypeKind::kImplicit || dtype.is_signed;
  pd.decl_is_signed = dtype.is_signed;
  pd.decl_type_implicit = dtype.kind == DataTypeKind::kImplicit;
  if (pd.has_decl_range || pd.has_decl_type) {
    pd.decl_width = EvalTypeWidth(dtype);
  }
}

void PopulateParamTypeInfo(RtlirParamDecl& pd, const DataType& dtype,
                           const TypedefMap& typedefs, const ScopeMap& scope) {
  pd.has_decl_range = dtype.packed_dim_left != nullptr;
  pd.has_decl_type = dtype.kind != DataTypeKind::kImplicit || dtype.is_signed;
  pd.decl_is_signed = dtype.is_signed;
  pd.decl_type_implicit = dtype.kind == DataTypeKind::kImplicit;
  if (pd.has_decl_range || pd.has_decl_type) {
    pd.decl_width = EvalTypeWidth(dtype, typedefs, scope);
  }
}

void RecordParamDeclRange(RtlirParamDecl& pd, const DataType& dtype,
                          const ScopeMap& scope) {
  if (!dtype.packed_dim_left || !dtype.packed_dim_right) return;
  auto left = ConstEvalInt(dtype.packed_dim_left, scope);
  auto right = ConstEvalInt(dtype.packed_dim_right, scope);
  if (!left || !right) return;
  pd.decl_range_left = *left;
  pd.decl_range_right = *right;
  pd.has_decl_range_bounds = true;
}

bool ParamExpectsIntegerValue(const RtlirParamDecl& pd, const DataType& dtype) {
  // §6.20.2: a value parameter is in an integer context — and so subject to the
  // real-to-integer conversion of §6.12.1 — when it carries a packed range or
  // an explicit non-real data type. A bare (untyped) parameter or one declared
  // real takes a real value instead and is not converted here.
  return pd.has_decl_range || (pd.has_decl_type && !IsRealType(dtype.kind));
}

// §6.20.2 (printed page 126): a parameter declared with neither type nor
// range takes the type of its final value, and where that value is real the
// parameter is real -- the clause's own `parameter r = 5.7`, which its
// comment calls a real parameter. Its expression is real where it has a real
// operand (HasRealOperand): a real literal, or a name standing for a real
// parameter already resolved. Tried for a declared real type alone, `r` was
// folded as an integer, which a real literal is not, and stayed unresolved,
// reading 0.0 at the run.
static bool TakesRealFromValue(const RtlirParamDecl& pd, const Expr* init,
                               const DataType& dtype) {
  return dtype.kind == DataTypeKind::kImplicit && !pd.has_decl_range &&
         !pd.has_decl_type && HasRealOperand(init);
}

bool TryFoldRealParamValue(RtlirParamDecl& pd, const Expr* init,
                           const DataType& dtype, const ScopeMap& scope) {
  if (!IsRealType(dtype.kind) && !TakesRealFromValue(pd, init, dtype))
    return false;
  auto rval = ConstEvalReal(init, scope);
  if (!rval) return false;
  pd.resolved_real = *rval;
  pd.is_real_value = true;
  pd.is_resolved = true;
  return true;
}

// Records the characters of a §6.16 string parameter's value on its
// declaration, so that a later fold can read the length §6.16.1's `len()`
// returns. Does not touch resolved_value, which the §11.10 packed fold has
// already written and which the rest of the elaborator reads. The characters
// are copied into `arena` because resolved_string is a std::string_view and
// outlives the std::string ConstEvalString returns. Returns false, having
// changed nothing, when `init` is not a string literal, which is the answer a
// caller replacing an already-recorded value needs.
bool RecordStringParamChars(RtlirParamDecl& pd, const Expr* init,
                            Arena& arena) {
  auto chars = ConstEvalString(init);
  if (!chars) return false;
  pd.resolved_string = {arena.AllocString(chars->c_str(), chars->size()),
                        chars->size()};
  pd.is_string_value = true;
  return true;
}

// The same recording where the declared type decides whether it happens at all.
// Does nothing for a parameter of any other declared type, because §5.13
// associates `len()` with `string` alone, which is what leaves a string literal
// initializing or overriding an integral parameter the §11.10 packed number
// §11.10 makes it.
void RecordStringParamValue(RtlirParamDecl& pd, const Expr* init,
                            const DataType* dtype, Arena& arena) {
  if (!dtype || dtype->kind != DataTypeKind::kString) return;
  RecordStringParamChars(pd, init, arena);
}

int64_t ConvertOverrideValue(int64_t value, const RtlirParamDecl& pd) {
  // §6.20.2: a parameter declared with an explicit range, or with an explicit
  // (non-implicit) data type, keeps the sign and range of its declaration; a
  // value override does not change them, so the incoming value is coerced into
  // the declared width. A parameter with no range and only an implicit type
  // (including a bare `signed`) instead takes its range from the final value
  // assigned, so the override value passes through unchanged.
  bool has_fixed_width =
      pd.has_decl_range || (pd.has_decl_type && !pd.decl_type_implicit);
  if (!has_fixed_width) return value;
  uint32_t w = pd.decl_width;
  if (w == 0 || w >= 64) return value;
  uint64_t mask = (uint64_t{1} << w) - 1;
  uint64_t masked = static_cast<uint64_t>(value) & mask;
  if (pd.decl_is_signed) {
    uint64_t sign_bit = uint64_t{1} << (w - 1);
    if (masked & sign_bit) masked |= ~mask;
  }
  return static_cast<int64_t>(masked);
}

// Resolve the value of a parameter that has a default expression (pval) but no
// instantiation override. Handles the §6.20.7 unbounded-parameter forms and the
// §6.20.2 integer/real constant folding. refers_to_unbounded and
// contains_dollar are precomputed by the caller because they require Elaborator
// member helpers; has_param_type / param_type describe the optional declared
// data type.
// §6.20.7: an unbounded ($) parameter value, or a reference to another
// unbounded parameter, makes this parameter unbounded too. Returns true when
// the value was recognized as unbounded (and pd updated), so the caller can
// stop.
static bool TryResolveUnboundedParamValue(RtlirParamDecl& pd, const Expr* pval,
                                          bool refers_to_unbounded) {
  if (pval->kind == ExprKind::kIdentifier && pval->text == "$") {
    pd.is_unbounded = true;
    return true;
  }
  if (pval->kind == ExprKind::kIdentifier && refers_to_unbounded) {
    // §6.20.7: assigning a $ (unbounded) parameter to another parameter is
    // legal; the assigned-to parameter is itself unbounded.
    pd.is_unbounded = true;
    return true;
  }
  return false;
}

// Fold a parameter's default expression into a concrete value: prefer an
// integer constant, then (for integer-typed parameters) a real constant rounded
// per §6.12.1. §11.6.1 (printed page 299): the default is the right-hand side
// of an assignment to the parameter, so its context-determined operands are
// sized by the declared width and the value is cut to it (FoldParamValue), as
// a parameter among the items has its value folded; folded self-determined,
// `parameter logic [95:0] X = 3 ** 50` in a port list raised 3 at 32 bits.
static void FoldParamConstantValue(RtlirParamDecl& pd, const Expr* pval,
                                   const ScopeMap& scope, bool has_param_type,
                                   const DataType* param_type) {
  if (has_param_type && param_type != nullptr &&
      TryFoldRealParamValue(pd, pval, *param_type, scope))
    return;
  // §6.20.2 (printed page 127): an integer-typed parameter set from a real
  // expression is converted to an integer per §6.12.1 (round to nearest,
  // ties away from zero), ahead of the integer fold as ResolveParamConstValue
  // (elaborator_items_params.cpp) orders the two, since that fold reads a
  // name standing for a real parameter as 0. An integral expression the
  // integer fold declined -- `0 ** -1`, x under §11.4.3's Table 11-4
  // (printed 276) -- was refolded as a real here, through std::pow(0, -1)
  // and std::llround of the inf it makes, and stays unresolved now.
  std::optional<int64_t> val;
  if (!pd.is_type_param && has_param_type &&
      ParamExpectsIntegerValue(pd, *param_type))
    val = FoldRealValueAsInteger(pval, scope);
  if (!val) val = FoldParamValue(pd, pval, scope);
  if (val) {
    pd.resolved_value = *val;
    pd.is_resolved = true;
    // §6.20.2 (printed page 126): the width and signedness of the default of
    // a parameter port declared with neither type nor range, and the words
    // above bit 63 of one declared wider, are recorded as a parameter among
    // the items has them recorded (ResolveParamConstValue in
    // elaborator_items_params.cpp), for the storage the lowerer gives the
    // instance that keeps the default (ParamStorageShapeOf in
    // src/simulator/lowerer_register.cpp); an override records its own
    // (ApplyParamOverride).
    RecordResolvedHighWords(pd, pval, scope);
  }
}

// §6.20: a parameter's default value expression together with the
// classification of that expression and the parameter's declared type. These
// fields describe a single domain object - the value being assigned to the
// parameter - so they are bundled and passed together when resolving the
// parameter's concrete value.
struct ParamValueExpr {
  const Expr* pval;          // the default value expression
  std::string_view pname;    // name of the parameter receiving the value
  bool refers_to_unbounded;  // §6.20.7: expr is an unbounded ($) parameter ref
  bool contains_dollar;      // §6.20.7: expr contains a $ subexpression
  bool has_param_type;       // parameter has an explicit declared data type
  const DataType* param_type;  // §6.20.2: that declared type (null if none)
};

static void ResolveUnresolvedParamValue(RtlirParamDecl& pd,
                                        const ParamValueExpr& val,
                                        const ScopeMap& scope,
                                        DiagEngine& diag) {
  if (TryResolveUnboundedParamValue(pd, val.pval, val.refers_to_unbounded)) {
    return;
  }
  if (val.contains_dollar) {
    // §6.20.7: $ must be the entire, self-contained parameter value; it
    // may not be combined with operators or selects in this context.
    diag.Error(val.pval->range.start,
               std::format("'$' may only be assigned to parameter '{}' "
                           "as a complete, self-contained expression",
                           val.pname),
               Subclause("6.20.7"));
  }
  FoldParamConstantValue(pd, val.pval, scope, val.has_param_type,
                         val.param_type);
}

// §11.6.1 (printed page 299) with §23.10.2 (printed 766): the override's
// expression is the right-hand side of an assignment to the parameter, so
// its context-determined operands are sized by the declared width as a
// declaration's own value's are. The instantiation site folded it
// self-determined, knowing nothing of the parameter it was for, so `c
// #(.P(8'hAB << 8)) u()` over `parameter [15:0] P` gave P 0. The expression
// is folded again here in the declared context, against the instantiating
// module's parameters as `assigns` took them, and only where a
// self-determined fold against that same scope reproduces the value the
// site folded: the site's scope may hold a name -- a generate block's
// parameter, a compilation unit's -- this one does not, under which a value
// the source did not write would be read. Empty where the declaration fixes
// no width, and where the fold does not reproduce the site's value.
static std::optional<int64_t> ContextOverrideValue(
    const RtlirParamDecl& pd, const Elaborator::ParamOverride& ovr,
    const ScopeMap& scope) {
  if (DeclaredFoldContext(pd).width == 0) return std::nullopt;
  auto self = ConstEvalInt(ovr.value_expr, scope);
  if (!self || *self != ovr.value) return std::nullopt;
  return FoldParamValue(pd, ovr.value_expr, scope);
}

// Apply an instantiation override (if any) to a parameter, coercing the value
// to the declared width per §6.20.2. Returns true when an override was applied.
//
// §6.16 is why `dtype` is here. A parameter declared string takes a value of
// arbitrary length, which the coerced int64_t above cannot hold past eight
// characters, so the override's own expression is folded a second time with the
// characters as the answer. RecordStringParamValue does nothing unless `dtype`
// is string, which is what keeps a string literal overriding an integral
// parameter the §11.10 packed number it is there.
bool ApplyParamOverride(RtlirParamDecl& pd,
                        const InstanceParamAssignments& assigns,
                        std::string_view pname, const DataType* dtype,
                        Arena& arena) {
  const auto* ovr = FindParamOverride(assigns.params, pname);
  if (!ovr) return false;
  pd.resolved_value = ConvertOverrideValue(ovr->value, pd);
  pd.is_resolved = true;
  pd.from_override = true;
  // §6.20.2 has the declared range survive the override, and the folded int64
  // holds 64 bits of it, so the expression is kept for the simulator to
  // evaluate at the declared width. ResetAllConfigParams (§33.4.3's `#()`)
  // hands the declaration's own initializer back as the override, and that
  // expression is written in the declaring module, not the instantiating one,
  // which is what default_value already says of it.
  if (ovr->value_expr != pd.default_value) pd.override_expr = ovr->value_expr;
  // §23.10.2 (printed page 766): the override's expression is written in the
  // instantiating module, and its fold at elaboration reads the parameter's
  // words above bit 63 nowhere else -- the instantiating module's
  // registration, live from the item loop this instantiation is an item of,
  // is the one the expression's names mean something in, and the child's own
  // registration, under which the name is later read, cannot refold it. So
  // the words are recorded now, against that registration's parameters,
  // which `assigns` took from it: a parameter port is built while it is
  // still live, and a parameter among the items after the child's own has
  // replaced it. An expression that is the declaration's own initializer,
  // handed back by ResetAllConfigParams, stands in the declaring module and
  // is left to the refold there.
  if (pd.override_expr != nullptr) {
    if (auto in_context = ContextOverrideValue(pd, *ovr, assigns.scope))
      pd.resolved_value = ConvertOverrideValue(*in_context, pd);
    pd.override_scope = assigns.scope;
    pd.override_module = assigns.module;
    RecordResolvedHighWords(pd, pd.override_expr, assigns.scope);
  }
  RecordStringParamValue(pd, ovr->value_expr, dtype, arena);
  return true;
}

// What a parameter port declaration is built against, and the name table it is
// registered into. The three travel together because a parameter port cannot be
// built without the first two nor judged under §11.5.1 without the third, and
// etc/clang_tidy/src.yml caps a function at five parameters.
struct ParamPortCtx {
  const TypedefMap& typedefs;
  const ScopeMap& scope;
  std::unordered_set<std::string_view>& real_param_names;
};

// Build the non-value identity/type fields of a parameter declaration (name,
// localparam/type-param flags, declared-type info), and record a real-typed one
// in `ctx.real_param_names`. Value resolution is handled separately because it
// requires Elaborator member helpers.
//
// The registration is here rather than at the call site because §11.5.1 states
// "A bit-select or part-select of a scalar, or of a real variable or real
// parameter, shall be illegal", naming the parameter rather than the position
// the parameter was written in. PopulateValueParamInfo in
// src/elaborator/elaborator_items.cpp records a real parameter written in the
// module body into the same set, and CheckRealSelectNode in
// src/elaborator/elaborator_validate.cpp reads it for either position. A
// localparam port is recorded on the same terms, since §6.20.2 makes it a value
// parameter.
static RtlirParamDecl BuildParamDeclShell(const ModuleDecl* decl, size_t i,
                                          const ParamPortCtx& ctx,
                                          bool has_param_type) {
  const auto& [pname, pval] = decl->params[i];
  RtlirParamDecl pd;
  pd.name = pname;
  pd.default_value = pval;
  pd.is_resolved = false;
  pd.is_type_param = decl->type_param_names.count(pname) > 0;
  pd.is_localparam = decl->localparam_port_names.count(pname) > 0;
  if (has_param_type) {
    pd.decl_type = &decl->param_types[i];
    PopulateParamTypeInfo(pd, decl->param_types[i], ctx.typedefs, ctx.scope);
    RecordParamDeclRange(pd, decl->param_types[i], ctx.scope);
    if (IsRealType(decl->param_types[i].kind))
      ctx.real_param_names.insert(pname);
  }
  return pd;
}

void Elaborator::ElaborateParamPortList(const ModuleDecl* decl,
                                        const ParamList& params,
                                        RtlirModule* mod) {
  TypeParamValueCtx tp_ctx{typedefs_, class_names_, diag_};
  // The instantiating module is the one registered here, from the item loop
  // this instantiation is an item of, and its parameters are what the
  // assignments' expressions name.
  const InstanceParamAssignments kAssigns{params, RegisteredModuleScope(),
                                          RegisteredModule()};
  for (size_t i = 0; i < decl->params.size(); ++i) {
    const auto& [pname, pval] = decl->params[i];
    auto scope = BuildParamScope(mod);
    bool has_param_type = i < decl->param_types.size() &&
                          decl->type_param_names.count(pname) == 0;
    RtlirParamDecl pd = BuildParamDeclShell(
        decl, i, {typedefs_, scope, real_param_names_}, has_param_type);
    const DataType* param_type =
        has_param_type ? &decl->param_types[i] : nullptr;
    ApplyParamOverride(pd, kAssigns, pname, param_type, arena_);
    if (!pd.is_resolved && pval) {
      bool refers_to_unbounded = pval->kind == ExprKind::kIdentifier &&
                                 RefersToUnboundedParam(mod, pval->text);
      bool contains_dollar = ContainsDollarSubexpr(pval);
      ParamValueExpr val{
          pval,           pname,     refers_to_unbounded, contains_dollar,
          has_param_type, param_type};
      // §6.20.2 (printed page 126): the default is written in the declaring
      // module, so this module is the one registered while it is folded, as
      // it is for a parameter among the items: a real parameter port already
      // built, `parameter real a = 1.5`, is read as the real it is by a
      // later port's `parameter b = a * 2` from the registration alone, the
      // scope holding one integer per name. The override above stands in
      // the instantiating module and is folded under that one's
      // registration, which is why the guard opens here and not around the
      // loop.
      ParamRangeRegistryGuard default_guard(mod);
      ResolveUnresolvedParamValue(pd, val, scope, diag_);
      // §6.20.2 (printed page 126): an untyped port whose default is real is
      // a real parameter, recorded for §11.5.1 as BuildParamDeclShell records
      // a port declared real.
      if (pd.is_real_value) real_param_names_.insert(pname);
    }
    // Only where the value came from `pval`, the declaration's own initializer.
    // An overridden parameter no longer has that value, and ApplyParamOverride
    // has already recorded the characters of the one that replaced it.
    //
    // §6.16: registering this module is what lets a string parameter port
    // written in terms of an earlier one read that one's characters, since
    // ConstEvalString resolves a name against the registered module's
    // parameters. It is opened around this call alone rather than around the
    // loop, because ApplyParamOverride above folds an expression written in the
    // instantiating parent, and the parent's registration -- live from the item
    // loop this instantiation is an item of -- is the one that expression's
    // names mean something in.
    if (pval && has_param_type && !pd.from_override) {
      // §23.9 needs no scope installed beside this one. A parameter port list
      // is processed before any of the module's items, so no generate block's
      // parameter is in RtlirModule::params yet and no expression here stands
      // in a block; ParamRangeRegistryGuard leaves the prefixes empty, which is
      // what an expression among a module's own items wants.
      ParamRangeRegistryGuard param_range_guard(mod);
      RecordStringParamValue(pd, pval, param_type, arena_);
    }
    CheckTypeParamValueAssignable(decl, i, pval, scope, tp_ctx);
    mod->params.push_back(pd);
  }
}

// §23.10 (printed page 763) with §6.20.1 (printed 125): the parameter value
// assignments a module's body parameters read, installed by
// BodyParamAssignmentsGuard. Null unless a guard is live.
static const InstanceParamAssignments* g_body_param_assignments = nullptr;

BodyParamAssignmentsGuard::BodyParamAssignmentsGuard(
    const InstanceParamAssignments* assigns)
    : prev_(g_body_param_assignments) {
  g_body_param_assignments = assigns;
}

BodyParamAssignmentsGuard::~BodyParamAssignmentsGuard() {
  g_body_param_assignments = prev_;
}

const InstanceParamAssignments* BodyParamAssignments() {
  return g_body_param_assignments;
}

std::vector<std::string_view> OverridableParamNames(const ModuleDecl* decl) {
  std::vector<std::string_view> names;
  for (const auto& [pname, pval] : decl->params) {
    if (decl->localparam_port_names.count(pname) > 0) continue;
    names.push_back(pname);
  }
  // §6.20.1 (printed pages 125-126): with a parameter port list, even an
  // empty one, `parameter` among the items is a synonym for `localparam`;
  // without one the items are where the module's value parameters are
  // declared, which §23.10.2's own example, `vdff` with `parameter size = 1,
  // delay = 1;` in its body under `vdff #(10,15)` (printed 766), relies on.
  // The override path read the parameter port list alone before, so that
  // shape was refused as naming no parameter, and too many for an ordered
  // list of none.
  if (decl->has_param_port_list) return names;
  for (const ModuleItem* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl || item->is_localparam)
      continue;
    names.push_back(item->name);
  }
  return names;
}

// The parameter declaration among `decl`'s items named `pname`, or null: a
// `parameter` or `localparam`, value or type, written at the module's own
// level. A generate block's, a task's or a function's is not among the items
// and is none of these (§23.10.2, printed page 766).
static const ModuleItem* BodyParamDecl(const ModuleDecl* decl,
                                       std::string_view pname) {
  for (const ModuleItem* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->name == pname)
      return item;
  }
  return nullptr;
}

// Whether `pname` is a type parameter `decl` declares among its items and an
// instance's parameter value assignment may name: one OverridableParamNames
// lists, so of a module declared with no parameter port list (§6.20.1,
// printed pages 125-126), declared `parameter type` (§6.20.3, printed
// 127-128). Parser::ParseTypeParamDecl (src/parser/parser_types.cpp) marks
// such a declaration with a void data type, its default carried beside it.
static bool IsBodyTypeParam(const ModuleDecl* decl, std::string_view pname) {
  if (decl->has_param_port_list) return false;
  const ModuleItem* item = BodyParamDecl(decl, pname);
  return item != nullptr && !item->is_localparam &&
         item->data_type.kind == DataTypeKind::kVoid;
}

// The value of an assignment to a body type parameter is a type, which no
// fold answers, so it was dropped with the assignment, and `c #(.T(logic
// [7:0])) u()` over `module c; parameter type T = int; T x;` left x 32 bits
// wide. A parameter port list's type parameter takes its type from
// ApplyChildTypeParams (elaborator_module_inst.cpp) instead.
void PushInstParamAssignment(const ModuleDecl* child_decl,
                             std::string_view pname, const Expr* pexpr,
                             const ScopeMap& parent_scope,
                             Elaborator::ParamList& child_params) {
  if (IsBodyTypeParam(child_decl, pname)) {
    child_params.push_back({pname, 0, pexpr});
    return;
  }
  auto val = ConstEvalInt(pexpr, parent_scope);
  if (val) child_params.push_back({pname, *val, pexpr});
}

// Whether `pname` names a local parameter of `decl`, which §6.20.4 (printed
// page 128) puts beyond a defparam and any instance parameter value
// assignment: a localparam of the parameter port list, a `localparam` among
// the items, or a `parameter` among the items of a module with a parameter
// port list, even an empty one, which §6.20.1 (printed 125-126) makes a
// synonym for `localparam`. False for a name no parameter of `decl` bears.
static bool IsLocalParamOf(const ModuleDecl* decl, std::string_view pname) {
  if (decl->localparam_port_names.count(pname) > 0) return true;
  const ModuleItem* item = BodyParamDecl(decl, pname);
  return item != nullptr && (item->is_localparam || decl->has_param_port_list);
}

// Reports the use clause's assignment to `pname`, written at `loc`, where
// no parameter of `child_decl` may take it, and says whether it did. A local
// parameter's report is worded as DefparamOverrideAllowed
// (elaborator_defparam.cpp) words a defparam's; such an assignment was
// applied and ignored in silence before: `instance top.u use #(.P(5))` on
// `module c #(parameter W = 1); parameter P = 2;` left P at 2 and said
// nothing, ApplyBodyParamAssignment (elaborator_items_params.cpp) passing
// over a local parameter as §6.20.4 has it, and ElaborateParamPortList
// applying one to a localparam port outright. A name no parameter of the
// module bears is reported as ResolveNamedInstParams
// (elaborator_module_inst.cpp) reports `c #(.X(5)) u()`: §33.4.3 (printed
// page 940) has the clause assign by name alone, and §23.10.2.2 (printed
// 767) makes the name one the instantiated module specifies. Such a name
// passed as none of the module's local parameters and was applied to
// nothing in silence, `use #(.X(5))` on `module c; parameter P = 2;`
// reporting nothing.
static bool ConfigParamRefused(
    const ModuleDecl* child_decl,
    const std::unordered_set<std::string_view>& overridable,
    std::string_view pname, SourceLoc loc, DiagEngine& diag) {
  if (IsLocalParamOf(child_decl, pname)) {
    diag.Error(loc,
               std::format("configuration cannot override a local parameter: "
                           "'{}' of module '{}'",
                           pname, child_decl->name),
               Subclause("6.20.4"));
    return true;
  }
  if (overridable.count(pname) > 0) return false;
  diag.Error(
      loc,
      std::format("module '{}' has no parameter '{}'", child_decl->name, pname),
      Subclause("23.10.2.2"));
  return true;
}

std::vector<std::pair<std::string_view, Expr*>> AssignableConfigParams(
    const ModuleDecl* child_decl,
    const std::vector<std::pair<std::string_view, Expr*>>& override_params,
    SourceLoc loc, DiagEngine& diag) {
  const std::vector<std::string_view> kNames =
      OverridableParamNames(child_decl);
  const std::unordered_set<std::string_view> kOverridable(kNames.begin(),
                                                          kNames.end());
  std::vector<std::pair<std::string_view, Expr*>> assignable;
  assignable.reserve(override_params.size());
  for (const auto& entry : override_params) {
    if (ConfigParamRefused(child_decl, kOverridable, entry.first, loc, diag))
      continue;
    assignable.push_back(entry);
  }
  return assignable;
}

}  // namespace delta
