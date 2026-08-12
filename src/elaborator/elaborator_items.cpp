#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/concurrent_assertion_expr.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

namespace {

// §16.14.3: the optional pass statement (statement_or_null) of a cover
// statement shall not include any concurrent assert, assume, or cover
// statement. A procedural concurrent assertion is parsed as an
// assert/assume/cover-immediate Stmt that carries is_procedural_concurrent;
// ordinary immediate assertions leave that flag clear and remain permitted.
// Walk the pass-statement subtree — including the statements a block, fork,
// conditional, loop, or case nests — and return the first offending statement,
// or nullptr when the pass statement contains none.
const Stmt* FindConcurrentAssertionInPassStmt(const Stmt* s);

// The first procedural concurrent assertion reachable from any statement in
// `children`, or null when none of them contains one.
template <typename Stmts>
const Stmt* FindConcurrentAssertionInStmtList(const Stmts& children) {
  for (const Stmt* child : children) {
    if (const Stmt* hit = FindConcurrentAssertionInPassStmt(child)) return hit;
  }
  return nullptr;
}

const Stmt* FindConcurrentAssertionInPassStmt(const Stmt* s) {
  if (s == nullptr) return nullptr;
  if (s->is_procedural_concurrent && (s->kind == StmtKind::kAssertImmediate ||
                                      s->kind == StmtKind::kAssumeImmediate ||
                                      s->kind == StmtKind::kCoverImmediate)) {
    return s;
  }
  if (const Stmt* hit = FindConcurrentAssertionInStmtList(s->stmts)) return hit;
  if (const Stmt* hit = FindConcurrentAssertionInStmtList(s->fork_stmts))
    return hit;
  const std::initializer_list<const Stmt*> kBranches = {
      s->then_branch, s->else_branch,      s->body,
      s->for_body,    s->assert_pass_stmt, s->assert_fail_stmt};
  if (const Stmt* hit = FindConcurrentAssertionInStmtList(kBranches))
    return hit;
  for (const CaseItem& ci : s->case_items) {
    if (const Stmt* hit = FindConcurrentAssertionInPassStmt(ci.body))
      return hit;
  }
  return nullptr;
}

}  // namespace

void Elaborator::ElaborateSpecparam(ModuleItem* item, RtlirModule* mod) {
  RtlirVariable var;
  var.name = ScopedName(item->name);
  if (item->data_type.packed_dim_left && item->data_type.packed_dim_right) {
    var.width = EvalTypeWidth(item->data_type);
    if (var.width == 0) var.width = 32;
  } else if (item->init_expr &&
             item->init_expr->kind == ExprKind::kIntegerLiteral) {
    // §6.20.5: a specify parameter with no range specification takes the range
    // of its final value. A sized integer literal carries that width directly
    // (a 4'd5 value is 4 bits); an unsized literal is 32 bits. Non-literal or
    // non-integer initializers keep the 32-bit default.
    uint32_t w = InferExprWidth(item->init_expr, typedefs_);
    var.width = w == 0 ? 32 : w;
  } else {
    var.width = 32;
  }
  var.init_expr = item->init_expr;
  mod->variables.push_back(var);
}

bool IsNameDeclared(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) return true;
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) return true;
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) return true;
  }
  return false;
}

// True when `name` is a parameter of `mod`. A parameter is a declaration of the
// module like a net or a variable, but it is held apart from both, so the
// implicit-net rule has to ask about it separately.
static bool IsParamDeclared(std::string_view name, const RtlirModule* mod) {
  for (const auto& p : mod->params) {
    if (p.name == name) return true;
  }
  return false;
}

bool Elaborator::MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                                        RtlirModule* mod) {
  if (IsNameDeclared(name, mod)) return true;
  // §6.10 gives an implicit net to an identifier used in a port connection or
  // on the left of a continuous assignment only when it is not declared. A
  // parameter is declared, and §23.3.3.3 lets any expression drive an input
  // port, so a parameter named as a port actual is the expression that drives
  // it. Creating a scalar net of the same name here would instead shadow the
  // parameter with an undriven wire and deliver zero to the port.
  if (IsParamDeclared(name, mod)) return true;
  if (unit_->default_nettype == NetType::kNone) {
    diag_.Error(loc,
                std::format("implicit net '{}' forbidden by "
                            "`default_nettype none",
                            name),
                Subclause("22.8"));
    return false;
  }
  // §6.10: an identifier used in an instance terminal/port-connection list or
  // on the left side of a continuous assignment gets an implicit scalar net of
  // the default net type. It shares the implicit-net constructor with the
  // port-expression case; here the width is scalar and the net is unsigned.
  RtlirNet net =
      MakeImplicitPortNet(ScopedName(name), /*port_width=*/1,
                          /*port_is_signed=*/false, unit_->default_nettype);
  mod->nets.push_back(net);
  declared_names_.insert(name);
  net_names_.insert(name);
  return true;
}

void Elaborator::ValidateTypenameAsElabConstant(const Expr* init) {
  if (init->kind != ExprKind::kSystemCall) return;
  if (init->callee != "$typename") return;
  if (init->args.empty()) return;
  const auto* arg = init->args[0];
  if (arg->kind == ExprKind::kMemberAccess) {
    diag_.Error(arg->range.start,
                "$typename argument in elaboration-time-constant context "
                "shall not contain hierarchical references",
                Subclause("20.6.1"));
    return;
  }
  if (arg->kind != ExprKind::kSelect) return;
  auto it = var_array_info_.find(arg->base->text);
  if (it == var_array_info_.end()) return;
  if (!it->second.is_dynamic && !it->second.is_assoc) return;
  diag_.Error(arg->range.start,
              "$typename argument in elaboration-time-constant context "
              "shall not reference elements of dynamic objects",
              Subclause("20.6.1"));
}

namespace {

// §6.20.3: a data type parameter (parameter type) can only be set to a data
// type. The parser marks a type parameter with a void data type; if such a
// parameter received an ordinary value expression instead of a type, it has
// been set to a non-type and must be rejected.
void CheckTypeParamNotSetToValue(const ModuleItem* item, DiagEngine& diag) {
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind == DataTypeKind::kImplicit &&
      item->init_expr != nullptr &&
      item->init_expr->kind != ExprKind::kTypeRef) {
    diag.Error(item->loc,
               std::format("type parameter '{}' can only be set to a data "
                           "type, not a value expression",
                           item->name),
               Subclause("6.20.3"));
  }
}

// §6.20.3: a type parameter declared with a leading basic-data-type keyword
// (enum, struct, union, class, or interface class) restricts its valid types;
// assigning a type that does not conform to that keyword is an error. The
// assigned type is resolved through any typedef chain first, and only a
// definite mismatch is flagged -- a still-named type is left alone, since it
// may resolve to a conforming type declared elsewhere.
//
// On a type-parameter item the restriction keyword is carried in
// forward_type_kind as: kEnum/kStruct/kUnion for those aggregate keywords,
// kNamed for a `class` restriction, and kVoid for `interface class` (see
// Parser::ParseTypeParamDecl).
// Follow a chain of typedef names to the concrete type behind it, stopping at
// a name with no definition. The hop limit keeps a cyclic typedef from looping.
const DataType* ResolveNamedTypeChain(const DataType* dtype,
                                      const TypedefMap& typedefs) {
  for (int hops = 0; hops < 8 && dtype->kind == DataTypeKind::kNamed; ++hops) {
    auto td = typedefs.find(dtype->type_name);
    if (td == typedefs.end()) break;
    dtype = &td->second;
  }
  return dtype;
}

// §6.20.3.1: a class (or interface class) type is always referenced by name, so
// a resolved concrete type -- a built-in scalar/vector, enum, struct, or union
// -- cannot be a class and does not conform. A type still named after
// resolution is left alone: it may be a class declared elsewhere.
void CheckTypeParamIsClass(const ModuleItem* item, DataTypeKind fwd,
                           const DataType& resolved, DiagEngine& diag) {
  if (resolved.kind == DataTypeKind::kNamed) return;
  diag.Error(
      item->loc,
      std::format("type parameter '{}' is restricted to a {} type but is "
                  "assigned a type that is not a class",
                  item->name,
                  fwd == DataTypeKind::kVoid ? "interface class" : "class"),
      Subclause("6.20.3.1"));
}

// §6.20.3.1: a type parameter restricted to enum, struct, or union conforms
// only if the type it is assigned resolves to that same kind.
void CheckTypeParamIsAggregateKind(const ModuleItem* item, DataTypeKind fwd,
                                   const DataType& resolved, DiagEngine& diag) {
  if (resolved.kind == DataTypeKind::kNamed || resolved.kind == fwd) return;
  static const auto kBasicName = [](DataTypeKind k) -> std::string_view {
    switch (k) {
      case DataTypeKind::kEnum:
        return "enum";
      case DataTypeKind::kStruct:
        return "struct";
      case DataTypeKind::kUnion:
        return "union";
      default:
        return "type";
    }
  };
  diag.Error(item->loc,
             std::format("type parameter '{}' is assigned a type that does "
                         "not conform to the required {} kind",
                         item->name, kBasicName(fwd)),
             Subclause("6.20.3.1"));
}

void CheckTypeParamConformsToForwardKind(const ModuleItem* item, bool is_type,
                                         const TypedefMap& typedefs,
                                         DiagEngine& diag) {
  if (!is_type) return;
  DataTypeKind fwd = item->forward_type_kind;
  bool aggregate_restriction = fwd == DataTypeKind::kEnum ||
                               fwd == DataTypeKind::kStruct ||
                               fwd == DataTypeKind::kUnion;
  bool class_restriction =
      fwd == DataTypeKind::kNamed || fwd == DataTypeKind::kVoid;
  if (!aggregate_restriction && !class_restriction) return;

  const DataType* resolved =
      ResolveNamedTypeChain(&item->typedef_type, typedefs);
  if (class_restriction) {
    CheckTypeParamIsClass(item, fwd, *resolved, diag);
    return;
  }
  CheckTypeParamIsAggregateKind(item, fwd, *resolved, diag);
}

// Fills the value-parameter type information on `pd` and, per §11.5.1, records
// a real-typed parameter as a scalar so any later bit/part select is rejected.
void PopulateValueParamInfo(
    RtlirParamDecl& pd, const ModuleItem* item,
    std::unordered_set<std::string_view>& scalar_var_names) {
  PopulateParamTypeInfo(pd, item->data_type);
  DataTypeKind pk = item->data_type.kind;
  if (pk == DataTypeKind::kReal || pk == DataTypeKind::kShortreal ||
      pk == DataTypeKind::kRealtime) {
    scalar_var_names.insert(item->name);
  }
}

// Const-evaluates a parameter's initializer against `scope` and records the
// resolved value on `pd`. §6.20.2: a parameter declared real takes a real
// value, and an integer-typed parameter initialized from a real constant rounds
// to the nearest integer (ties away from zero).
void ResolveParamConstValue(RtlirParamDecl& pd, const ModuleItem* item,
                            bool is_type, const ScopeMap& scope) {
  // The real fold comes first, because an integer fold of a real-typed
  // parameter's initializer succeeds whenever the value happens to have no
  // fraction and would then store it as the integer it is not.
  if (!is_type &&
      TryFoldRealParamValue(pd, item->init_expr, item->data_type, scope))
    return;
  auto val = ConstEvalInt(item->init_expr, scope);
  if (val) {
    pd.resolved_value = *val;
    pd.is_resolved = true;
  } else if (!is_type && ParamExpectsIntegerValue(pd, item->data_type)) {
    if (auto rval = ConstEvalReal(item->init_expr, scope)) {
      pd.resolved_value = std::llround(*rval);
      pd.is_resolved = true;
    }
  }
}

}  // namespace

void Elaborator::ElaborateParamDecl(ModuleItem* item, RtlirModule* mod) {
  bool is_type = item->data_type.kind == DataTypeKind::kVoid &&
                 item->typedef_type.kind != DataTypeKind::kImplicit;

  // §6.23/§6.20.3: a type-parameter default written with the type operator,
  // e.g. `localparam type T = type(int)`, arrives as a kTypeRef init expression
  // (its text is the inner type name) rather than a typedef_type. Resolve it to
  // a concrete type so dependent declarations elaborate against the chosen
  // type, carrying the built-in's implicit signedness (so `T x` is signed for
  // int). §8.23 also permits a class scope resolution to prefix that type name,
  // as in `type(Frame::payload_t)`, which the kTypeRef expression carries in
  // scope_prefix. Resolve that form through the class instead, and leave
  // typedef_type unchanged when the class or its typedef is not visible.
  if (!is_type && item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind == DataTypeKind::kImplicit && item->init_expr &&
      item->init_expr->kind == ExprKind::kTypeRef &&
      !item->init_expr->text.empty()) {
    if (item->init_expr->scope_prefix.empty()) {
      item->typedef_type = TypeNameToDataType(item->init_expr->text);
    } else if (const DataType* scoped =
                   FindClassScopedTypedefType(item->init_expr->scope_prefix,
                                              item->init_expr->text, unit_)) {
      item->typedef_type = *scoped;
    }
    is_type = item->typedef_type.kind != DataTypeKind::kImplicit;
  }

  CheckTypeParamNotSetToValue(item, diag_);
  CheckTypeParamConformsToForwardKind(item, is_type, typedefs_, diag_);

  if (is_type) {
    typedefs_[item->name] = item->typedef_type;
  }
  RtlirParamDecl pd;
  pd.name = item->name;
  pd.is_type_param = is_type;

  pd.is_localparam = item->is_localparam || mod->has_param_port_list;
  pd.default_value = item->init_expr;
  if (!is_type) {
    PopulateValueParamInfo(pd, item, scalar_var_names_);
    // §11.5.1: a select on this parameter names bits by their index in the
    // range it is declared with, so keep the two bounds. They are folded
    // against the parameters already elaborated, which is what a bound written
    // in terms of an earlier parameter needs.
    RecordParamDeclRange(pd, item->data_type, BuildParamScope(mod));
  }

  // §6.20.7: a parameter is unbounded if it is assigned a literal '$', or if it
  // is assigned another (unbounded) parameter; the assigned-to parameter is
  // itself unbounded in that case.
  if (item->init_expr && item->init_expr->kind == ExprKind::kIdentifier &&
      (item->init_expr->text == "$" ||
       RefersToUnboundedParam(mod, item->init_expr->text))) {
    pd.is_unbounded = true;
  } else if (item->init_expr) {
    if (ContainsDollarSubexpr(item->init_expr)) {
      // §6.20.7: $ must be the entire, self-contained parameter value; it may
      // not be combined with operators or selects in this context.
      diag_.Error(item->loc,
                  std::format("'$' may only be assigned to parameter '{}' as a "
                              "complete, self-contained expression",
                              item->name),
                  Subclause("6.20.7"));
    }
    ValidateTypenameAsElabConstant(item->init_expr);
    auto scope = BuildParamScope(mod);
    ResolveParamConstValue(pd, item, is_type, scope);
  }
  mod->params.push_back(pd);

  const_names_.insert(item->name);
}

namespace {

// §28.3.6: validates the per-terminal bit-lengths of a gate/switch instance
// array whose instance range has already been confirmed present. `scope` is the
// caller's parameter scope used to evaluate the range bounds. An interconnect
// terminal must match the instance-array length exactly; an ordinary terminal
// must be either scalar-width (broadcast) or equal to the array length.
void CheckGateInstanceArrayTerminalWidths(
    const ModuleItem* item, const RtlirModule* mod, const ScopeMap& scope,
    const std::unordered_set<std::string_view>& interconnect_names,
    DiagEngine& diag) {
  auto lhi = ConstEvalInt(item->inst_range_left, scope);
  auto rhi = ConstEvalInt(item->inst_range_right, scope);
  if (!lhi || !rhi) {
    diag.Error(item->loc,
               "gate or switch instance range bound is not a constant "
               "expression",
               Subclause("28.3.5"));
    return;
  }
  auto array_len = static_cast<uint32_t>(std::abs(*lhi - *rhi) + 1);
  for (auto* term : item->gate_terminals) {
    uint32_t w = LookupLhsWidth(term, mod);
    if (w == 0) continue;
    bool is_interconnect = term && term->kind == ExprKind::kIdentifier &&
                           interconnect_names.count(term->text) != 0;
    if (is_interconnect) {
      if (w != array_len) {
        diag.Error(item->loc,
                   "interconnect terminal of a gate instance array "
                   "must have a bit-length equal to the instance-array "
                   "length",
                   Subclause("28.3.6"));
        break;
      }
      continue;
    }
    if (w != 1 && w != array_len) {
      diag.Error(item->loc,
                 "gate array terminal width does not match either "
                 "the per-instance port width or the instance-array "
                 "length",
                 Subclause("28.3.6"));
      break;
    }
  }
}

// Emits the redeclaration and dynamic-override-specifier diagnostics for a
// function or task declaration item. Records the name in `declared_names`.
void CheckFunctionDeclDiagnostics(
    const ModuleItem* item,
    std::unordered_set<std::string_view>& declared_names, DiagEngine& diag) {
  if (!item->name.empty() && !declared_names.insert(item->name).second) {
    diag.Error(item->loc, std::format("redeclaration of '{}'", item->name),
               Subclause("23.9"));
  }
  if (item->method_class.empty() &&
      (item->is_method_initial || item->is_method_extends ||
       item->is_method_final)) {
    diag.Error(item->loc,
               "dynamic_override_specifiers shall only be legal on "
               "method declarations inside a non-interface class scope",
               Subclause("8.20"));
  }
}

// Emits the gate-instance name-conflict and redeclaration diagnostics. Records
// the instance name in `declared_names`.
void CheckGateInstNameDiagnostics(
    const ModuleItem* item,
    std::unordered_set<std::string_view>& declared_names, DiagEngine& diag) {
  if (!item->gate_inst_name.empty() && !item->gate_terminals.empty() &&
      item->gate_terminals[0] &&
      item->gate_terminals[0]->kind == ExprKind::kIdentifier &&
      item->gate_terminals[0]->text == item->gate_inst_name) {
    diag.Error(item->loc,
               std::format("gate instance name '{}' conflicts with its "
                           "output net",
                           item->gate_inst_name),
               Subclause("23.9"));
  }
  if (!item->gate_inst_name.empty() &&
      !declared_names.insert(item->gate_inst_name).second) {
    diag.Error(item->loc,
               std::format("redeclaration of '{}'", item->gate_inst_name),
               Subclause("23.9"));
  }
}

// Emits the UDP-instance redeclaration diagnostic and records the instance
// name.
void CheckUdpInstNameDiagnostics(
    const ModuleItem* item,
    std::unordered_set<std::string_view>& declared_names, DiagEngine& diag) {
  if (!item->gate_inst_name.empty() &&
      !declared_names.insert(item->gate_inst_name).second) {
    diag.Error(item->loc,
               std::format("redeclaration of '{}'", item->gate_inst_name),
               Subclause("23.9"));
  }
}

// Builds an RTLIR import record from an import-declaration item and appends it
// to the module's import list.
void RecordImportDecl(const ModuleItem* item, RtlirModule* mod) {
  RtlirImport imp;
  imp.package_name = item->import_item.package_name;
  imp.item_name = item->import_item.item_name;
  imp.is_wildcard = item->import_item.is_wildcard;
  mod->imports.push_back(imp);
}

// Records a class declaration's name (and parameterized status) and pushes the
// class decl onto the module per §8.
void RecordClassDecl(
    const ModuleItem* item, RtlirModule* mod,
    std::unordered_set<std::string_view>& class_names,
    std::unordered_set<std::string_view>& parameterized_class_names) {
  if (!item->class_decl) return;
  class_names.insert(item->class_decl->name);
  if (!item->class_decl->params.empty()) {
    parameterized_class_names.insert(item->class_decl->name);
  }
  mod->class_decls.push_back(item->class_decl);
}

// §6.10: every undeclared identifier in a primitive/alias terminal list becomes
// an implicit scalar net; `make_net` creates one net per identifier terminal.
template <typename MakeNet>
void CreateImplicitNetsForTerminals(const std::vector<Expr*>& terminals,
                                    SourceLoc loc, MakeNet&& make_net) {
  for (auto* term : terminals) {
    if (term && term->kind == ExprKind::kIdentifier) {
      make_net(term->text, loc);
    }
  }
}

bool HasInstanceArrayRange(const ModuleItem* item) {  // §28.3.6
  return item->inst_range_left != nullptr && item->inst_range_right != nullptr;
}

bool IsStaticDeferredAssertion(const ModuleItem* item) {  // §16.4.3
  return item->body != nullptr && item->body->is_deferred;
}

}  // namespace

void Elaborator::ElaborateItem(ModuleItem* item, RtlirModule* mod) {
  if (ElaborateDeclItem(item, mod)) return;
  ElaborateBehavioralItem(item, mod);
}

// Declarations, types, instances, and structural items (§6, §23, §25, §28).
bool Elaborator::ElaborateDeclItem(ModuleItem* item, RtlirModule* mod) {
  auto make_implicit_net = [&](std::string_view n, SourceLoc l) {  // §6.10
    MaybeCreateImplicitNet(n, l, mod);
  };
  switch (item->kind) {
    case ModuleItemKind::kNetDecl:
      ElaborateNetDecl(item, mod);
      return true;
    case ModuleItemKind::kVarDecl:
      ElaborateVarDecl(item, mod);
      return true;
    case ModuleItemKind::kContAssign:
      ElaborateContAssign(item, mod);
      return true;
    case ModuleItemKind::kModuleInst:
      ElaborateModuleInst(item, mod);
      return true;
    case ModuleItemKind::kParamDecl:
      ElaborateParamDecl(item, mod);
      return true;
    case ModuleItemKind::kTypedef:
      ElaborateTypedef(item, mod);
      return true;
    case ModuleItemKind::kNettypeDecl:
      ElaborateNettypeDecl(item, mod);
      return true;
    case ModuleItemKind::kGateInst:
      CheckGateInstNameDiagnostics(item, declared_names_, diag_);
      CreateImplicitNetsForTerminals(item->gate_terminals, item->loc,
                                     make_implicit_net);
      if (HasInstanceArrayRange(item)) {
        CheckGateInstanceArrayTerminalWidths(item, mod, BuildParamScope(mod),
                                             interconnect_names_, diag_);
      }
      ValidateBidirectionalSwitchConnections(item, mod, diag_,
                                             nettype_canonical_);
      ValidatePrimitiveOutputTerminalWidths(item, mod, BuildParamScope(mod),
                                            diag_);
      ElaborateGateInst(item, mod, arena_);
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      return true;
    case ModuleItemKind::kUdpInst:
      CheckUdpInstNameDiagnostics(item, declared_names_, diag_);
      CreateImplicitNetsForTerminals(item->gate_terminals, item->loc,
                                     make_implicit_net);
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      return true;
    case ModuleItemKind::kSpecparam:
      specparam_names_.insert(item->name);
      const_names_.insert(item->name);
      ElaborateSpecparam(item, mod);
      return true;
    case ModuleItemKind::kAlias: {
      CreateImplicitNetsForTerminals(item->alias_nets, item->loc,
                                     make_implicit_net);
      ValidateAlias(item, mod);
      RtlirAlias alias;
      alias.nets = item->alias_nets;
      mod->aliases.push_back(alias);
      return true;
    }
    case ModuleItemKind::kImportDecl:
      RecordImportDecl(item, mod);
      return true;
    case ModuleItemKind::kClassDecl:
      RecordClassDecl(item, mod, class_names_, parameterized_class_names_);
      return true;
    default:
      return false;
  }
}

// Processes, generates, subroutines, assertions, and remaining items (§9, §16,
// §13, §27).
bool Elaborator::ElaborateBehavioralItem(ModuleItem* item, RtlirModule* mod) {
  const ProcessBuildEnv kEnv{arena_, diag_, &func_decls_, &const_names_};
  switch (item->kind) {
    case ModuleItemKind::kInitialBlock:
      AddProcess(RtlirProcessKind::kInitial, item, mod,
                 ProcessBuildEnv{arena_, diag_});
      return true;
    case ModuleItemKind::kFinalBlock:
      AddProcess(RtlirProcessKind::kFinal, item, mod,
                 ProcessBuildEnv{arena_, diag_});
      return true;
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
      AddProcess(MapAlwaysKind(item->always_kind), item, mod, kEnv);
      return true;
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
    case ModuleItemKind::kGenerateFor:
      pending_generates_.push_back({item, mod});
      return true;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
      CheckFunctionDeclDiagnostics(item, declared_names_, diag_);
      ValidateFunctionBody(item);
      ValidateFunctionArgDefaultsScope(item);
      mod->function_decls.push_back(item);
      return true;
    case ModuleItemKind::kElabSystemTask:
      ValidateElabSystemTask(item, mod);
      return true;
    case ModuleItemKind::kDpiImport:
      ValidateDpiImport(item);
      mod->let_decls.push_back(item);
      return true;
    case ModuleItemKind::kLetDecl:
      ValidateLetDecl(item);
      let_names_.insert(item->name);
      mod->let_decls.push_back(item);
      return true;
    case ModuleItemKind::kSpecifyBlock:
      RegisterSpecifyBlockSpecparams(item, mod, specparam_names_, const_names_);
      mod->let_decls.push_back(item);
      return true;
    case ModuleItemKind::kCovergroupDecl:
      // §19.3 (footnote 29): the extends form of a covergroup is legal only
      // within a class. The grammar accepts `covergroup extends base ;` in any
      // scope, so the restriction is a semantic one applied here. A covergroup
      // declaration handled as a module item belongs to a module, interface,
      // checker, or program — class covergroups are elaborated as class
      // members and never reach this path — so an inherited base is illegal.
      if (!item->covergroup_extends_base.empty()) {
        diag_.Error(item->loc,
                    "a covergroup may only use 'extends' inside a class",
                    Subclause("19.3"));
      }
      mod->let_decls.push_back(item);
      return true;
    case ModuleItemKind::kDpiExport:
      mod->let_decls.push_back(item);
      return true;
    default:
      return ElaborateAssertionItem(item, mod);
  }
}

namespace {

// §16.6: an expression appearing in a concurrent assertion shall not reference
// a variable of chandle type. A concurrent assertion statement
// (assert/assume/cover/restrict property) keeps its property_spec expression in
// assert_expr, or, for the simple clocked boolean form, in the immediate body
// statement's assert_expr. Reports the first chandle reference once.
void CheckConcurrentAssertionNoChandle(const ModuleItem* item,
                                       const RtlirModule* mod,
                                       DiagEngine& diag) {
  const Expr* bodies[] = {item->assert_expr, item->body != nullptr
                                                 ? item->body->assert_expr
                                                 : nullptr};
  for (const Expr* b : bodies) {
    std::string_view ch = ConcurrentAssertionExprReferencedChandle(b, mod);
    if (!ch.empty()) {
      diag.Error(item->loc,
                 "concurrent assertion expression references chandle "
                 "variable \"" +
                     std::string(ch) + "\"",
                 Subclause("16.6"));
      return;
    }
  }
}

}  // namespace

void Elaborator::ElaborateSequenceDeclItem(ModuleItem* item, RtlirModule* mod) {
  sequence_names_.insert(item->name);
  mod->sequence_decls.push_back(item);
  // §16.8: a cyclic dependency among named sequences is an error. All sequence
  // decls are registered before elaboration (see ElaborateModule), so this DFS
  // sees the full graph regardless of declaration order.
  if (property_registry_.HasCyclicSequenceDependency(item)) {
    diag_.Error(item->loc,
                "cyclic dependency among named sequences involving \"" +
                    std::string(item->name) + "\"",
                Subclause("16.8"));
  }
  // §16.10: a formal-argument name may not be redeclared as a body local.
  ValidateNoFormalShadowedByBodyLocal(item);
  ValidateClockingBlock(item, mod);
}

// §16.12.1: an instance of a named property used as a property_expr operand of
// any property-building operator must, once substituted, yield a legal
// property_expr. A disable iff clause makes the flattened body a property_spec,
// which is not a legal operand -- so such a property may not carry a disable
// iff clause when it appears as an operand. The parser records the instances
// that stand as the operand of a prefix or infix property operator (not,
// s_nexttime, s_eventually, s_always, and the right operand of
// s_until/s_until_with) in prop_negated_instance_refs.
void Elaborator::CheckPropertyOperandInstances(const ModuleItem* item) {
  for (auto operand_ref : item->prop_negated_instance_refs) {
    const ModuleItem* callee = property_registry_.Find(operand_ref);
    if (callee == nullptr || callee->kind != ModuleItemKind::kPropertyDecl) {
      continue;
    }
    if (property_registry_.FlattenedDisableIffCount(callee) > 0) {
      diag_.Error(item->loc,
                  "property \"" + std::string(operand_ref) +
                      "\" has a disable iff clause and cannot be used as an "
                      "operand of a property operator in \"" +
                      std::string(item->name) + "\"",
                  Subclause("16.12.1"));
    }
  }
}

void Elaborator::ElaboratePropertyDeclItem(ModuleItem* item, RtlirModule* mod) {
  // §16.12: nesting of disable iff (explicitly or via property instantiation)
  // is forbidden; the §F.4.1 flattened count catches both.
  if (property_registry_.FlattenedDisableIffCount(item) > 1) {
    diag_.Error(item->loc,
                "property \"" + std::string(item->name) +
                    "\" nests disable iff clauses",
                Subclause("16.12"));
  }
  CheckPropertyOperandInstances(item);
  // §16.10: a formal-argument name may not be redeclared as a body local.
  ValidateNoFormalShadowedByBodyLocal(item);
  // §16.12.17 / §F.7: enforce the restrictions on recursive properties.
  ValidateRecursiveProperty(item);
  ValidateClockingBlock(item, mod);
}

void Elaborator::ElaborateAssertPropertyItem(ModuleItem* item,
                                             RtlirModule* mod) {
  CheckConcurrentAssertionNoChandle(item, mod, diag_);
  const ProcessBuildEnv kEnv{arena_, diag_, &func_decls_, &const_names_};
  // §16.4.3: a module-item deferred immediate assertion is a static deferred
  // assertion, modeled as an implicit always_comb procedure.
  if (IsStaticDeferredAssertion(item)) {
    AddProcess(RtlirProcessKind::kAlwaysComb, item, mod, kEnv);
    return;
  }
  // §16.14.5: a static concurrent assertion outside procedural code uses
  // `always` semantics. The parser captures the simple clocked boolean form as
  // a leading clock in item->sensitivity plus an immediate-assert body in
  // item->body; model it as a clocked process so the property is checked at
  // each leading clock edge.
  if (item->body != nullptr && !item->sensitivity.empty()) {
    AddProcess(RtlirProcessKind::kAlwaysFF, item, mod, kEnv);
    return;
  }
  ValidateClockingBlock(item, mod);
}

bool Elaborator::ElaborateAssertionItem(ModuleItem* item, RtlirModule* mod) {
  switch (item->kind) {
    case ModuleItemKind::kSequenceDecl:
      ElaborateSequenceDeclItem(item, mod);
      return true;
    case ModuleItemKind::kPropertyDecl:
      ElaboratePropertyDeclItem(item, mod);
      return true;
    case ModuleItemKind::kAssertProperty:
      ElaborateAssertPropertyItem(item, mod);
      return true;
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
      // §16.14.3: a cover statement's optional pass statement shall not include
      // any concurrent assert, assume, or cover statement.
      if (FindConcurrentAssertionInPassStmt(item->assert_pass_stmt) !=
          nullptr) {
        diag_.Error(item->loc,
                    "the pass statement of a cover statement may not include a "
                    "concurrent assert, assume, or cover statement",
                    Subclause("16.14.3"));
      }
      ValidateClockingBlock(item, mod);
      return true;
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kRestrictProperty:
    case ModuleItemKind::kClockingBlock:
      ValidateClockingBlock(item, mod);
      return true;
    default:
      // §23.10.4 kDefparam, kExportDecl, kDefaultDisableIff, kNestedModuleDecl,
      // and any remaining kind are no-ops at behavioral elaboration.
      return true;
  }
}

}  // namespace delta
