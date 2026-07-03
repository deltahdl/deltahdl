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
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/property_rewrite.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

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

bool Elaborator::MaybeCreateImplicitNet(std::string_view name, SourceLoc loc,
                                        RtlirModule* mod) {
  if (IsNameDeclared(name, mod)) return true;
  if (unit_->default_nettype == NetType::kNone) {
    diag_.Error(loc, std::format("implicit net '{}' forbidden by "
                                 "`default_nettype none",
                                 name));
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
                "shall not contain hierarchical references");
    return;
  }
  if (arg->kind != ExprKind::kSelect) return;
  auto it = var_array_info_.find(arg->base->text);
  if (it == var_array_info_.end()) return;
  if (!it->second.is_dynamic && !it->second.is_assoc) return;
  diag_.Error(arg->range.start,
              "$typename argument in elaboration-time-constant context "
              "shall not reference elements of dynamic objects");
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
                           item->name));
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
void CheckTypeParamConformsToForwardKind(const ModuleItem* item, bool is_type,
                                         const TypedefMap& typedefs,
                                         DiagEngine& diag) {
  if (!is_type) return;
  const DataTypeKind fwd = item->forward_type_kind;
  const bool aggregate_restriction = fwd == DataTypeKind::kEnum ||
                                     fwd == DataTypeKind::kStruct ||
                                     fwd == DataTypeKind::kUnion;
  const bool class_restriction =
      fwd == DataTypeKind::kNamed || fwd == DataTypeKind::kVoid;
  if (!aggregate_restriction && !class_restriction) return;

  const DataType* resolved = &item->typedef_type;
  for (int hops = 0; hops < 8 && resolved->kind == DataTypeKind::kNamed;
       ++hops) {
    auto td = typedefs.find(resolved->type_name);
    if (td == typedefs.end()) break;
    resolved = &td->second;
  }

  if (class_restriction) {
    // A class (or interface class) type is always referenced by name, so a
    // resolved concrete type -- a built-in scalar/vector, enum, struct, or
    // union -- cannot be a class and does not conform. A type still named after
    // resolution is left alone (it may be a class declared elsewhere).
    if (resolved->kind != DataTypeKind::kNamed) {
      diag.Error(item->loc,
                 std::format(
                     "type parameter '{}' is restricted to a {} type but is "
                     "assigned a type that is not a class",
                     item->name,
                     fwd == DataTypeKind::kVoid ? "interface class" : "class"));
    }
    return;
  }

  if (resolved->kind != DataTypeKind::kNamed && resolved->kind != fwd) {
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
                           item->name, kBasicName(fwd)));
  }
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
// resolved value on `pd`. §6.20.2: an integer-typed parameter initialized from
// a real constant rounds to the nearest integer (ties away from zero).
void ResolveParamConstValue(RtlirParamDecl& pd, const ModuleItem* item,
                            bool is_type, const ScopeMap& scope) {
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
  // int).
  if (!is_type && item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind == DataTypeKind::kImplicit && item->init_expr &&
      item->init_expr->kind == ExprKind::kTypeRef &&
      !item->init_expr->text.empty()) {
    item->typedef_type = TypeNameToDataType(item->init_expr->text);
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
                              item->name));
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
               "expression");
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
                   "length");
        break;
      }
      continue;
    }
    if (w != 1 && w != array_len) {
      diag.Error(item->loc,
                 "gate array terminal width does not match either "
                 "the per-instance port width or the instance-array "
                 "length");
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
    diag.Error(item->loc, std::format("redeclaration of '{}'", item->name));
  }
  if (item->method_class.empty() &&
      (item->is_method_initial || item->is_method_extends ||
       item->is_method_final)) {
    diag.Error(item->loc,
               "dynamic_override_specifiers shall only be legal on "
               "method declarations inside a non-interface class scope");
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
                           item->gate_inst_name));
  }
  if (!item->gate_inst_name.empty() &&
      !declared_names.insert(item->gate_inst_name).second) {
    diag.Error(item->loc,
               std::format("redeclaration of '{}'", item->gate_inst_name));
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
               std::format("redeclaration of '{}'", item->gate_inst_name));
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
      ValidatePrimitiveOutputTerminalWidths(item, mod, diag_);
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
  const ProcessBuildEnv kEnv{arena_, diag_, &func_decls_};
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
    case ModuleItemKind::kDpiExport:
      mod->let_decls.push_back(item);
      return true;
    default:
      return ElaborateAssertionItem(item, mod);
  }
}

bool Elaborator::ElaborateAssertionItem(ModuleItem* item, RtlirModule* mod) {
  const ProcessBuildEnv kEnv{arena_, diag_, &func_decls_};
  switch (item->kind) {
    case ModuleItemKind::kSequenceDecl:
      sequence_names_.insert(item->name);
      mod->sequence_decls.push_back(item);
      // §16.8: a cyclic dependency among named sequences is an error. All
      // sequence decls are registered before elaboration (see ElaborateModule),
      // so this DFS sees the full graph regardless of declaration order.
      if (property_registry_.HasCyclicSequenceDependency(item)) {
        diag_.Error(item->loc,
                    "cyclic dependency among named sequences involving \"" +
                        std::string(item->name) + "\" (§16.8)");
      }
      // §16.10: a formal-argument name may not be redeclared as a body local.
      ValidateNoFormalShadowedByBodyLocal(item);
      ValidateClockingBlock(item, mod);
      return true;
    case ModuleItemKind::kPropertyDecl: {
      // §16.12: nesting of disable iff (explicitly or via property
      // instantiation) is forbidden; the §F.4.1 flattened count catches both.
      int flat_disable_iff = property_registry_.FlattenedDisableIffCount(item);
      if (flat_disable_iff > 1) {
        diag_.Error(item->loc, "property \"" + std::string(item->name) +
                                   "\" nests disable iff clauses (§16.12)");
      }
      // §16.10: a formal-argument name may not be redeclared as a body local.
      ValidateNoFormalShadowedByBodyLocal(item);
      // §16.12.17 / §F.7: enforce the restrictions on recursive properties.
      ValidateRecursiveProperty(item);
      ValidateClockingBlock(item, mod);
      return true;
    }
    case ModuleItemKind::kAssertProperty:
      // §16.4.3: a module-item deferred immediate assertion is a static
      // deferred assertion, modeled as an implicit always_comb procedure.
      if (IsStaticDeferredAssertion(item)) {
        AddProcess(RtlirProcessKind::kAlwaysComb, item, mod, kEnv);
        return true;
      }
      // §16.14.5: a static concurrent assertion outside procedural code uses
      // `always` semantics. The parser captures the simple clocked boolean form
      // as a leading clock in item->sensitivity plus an immediate-assert body
      // in item->body; model it as a clocked process so the property is checked
      // at each leading clock edge.
      if (item->body != nullptr && !item->sensitivity.empty()) {
        AddProcess(RtlirProcessKind::kAlwaysFF, item, mod, kEnv);
        return true;
      }
      ValidateClockingBlock(item, mod);
      return true;
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
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

UdpDecl* Elaborator::FindUdpByName(std::string_view name) const {
  for (auto* u : unit_->udps) {
    if (u->name == name) return u;
  }
  return nullptr;
}

void Elaborator::ReclassifyForwardUdpInstances(const ModuleDecl* decl) {
  for (auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kModuleInst) continue;
    if (!FindUdpByName(item->inst_module)) continue;

    item->kind = ModuleItemKind::kUdpInst;
    item->gate_inst_name = item->inst_name;
    item->inst_name = {};
    item->gate_terminals.clear();
    item->gate_terminals.reserve(item->inst_ports.size());
    for (const auto& [pname, pexpr] : item->inst_ports) {
      item->gate_terminals.push_back(pexpr);
    }
    item->inst_ports.clear();
    item->inst_ports_implicit.clear();
  }
}

namespace {

// §25.9: returns the constant parameter-override values of a module instance
// when every override evaluates to a constant, or nullopt if the instance has
// no overrides or any override is non-constant.
std::optional<std::vector<int64_t>> TryConstEvalInstParams(
    const ModuleItem* item) {
  if (item->inst_params.empty()) return std::nullopt;
  std::vector<int64_t> values;
  for (const auto& param : item->inst_params) {
    const Expr* pexpr = param.second;
    if (pexpr == nullptr) return std::nullopt;
    auto v = ConstEvalInt(pexpr);
    if (!v) return std::nullopt;
    values.push_back(*v);
  }
  return values;
}

// §17.2/§17.7/§25.9: the kind of the enclosing scope that governs which nested
// items and instances are legal. `kind_word` is the diagnostic noun ("program"
// or "checker") used when either flag is set.
struct ParentScopeKind {
  bool is_program;
  bool is_checker;
  std::string_view kind_word;
};

// §25.9: the per-module lookup tables that record each instance's resolved kind
// (interface/checker/program) so later passes can validate references against
// the instantiated kind. Holds references to the elaborator member tables.
struct InstClassTables {
  std::unordered_map<std::string_view, std::string_view>& interface_inst_types;
  std::unordered_map<std::string_view, std::vector<int64_t>>&
      interface_inst_param_values;
  std::unordered_set<std::string_view>& checker_inst_names;
  std::unordered_set<std::string_view>& program_inst_names;
};

// §25.9: records a module-instance whose resolved child is an interface,
// checker, or program into the corresponding lookup table so later passes can
// validate references against the instantiated kind.
void ClassifyInstantiatedChild(const ModuleItem* item, const ModuleDecl* child,
                               InstClassTables& tables) {
  if (child->decl_kind == ModuleDeclKind::kInterface) {
    tables.interface_inst_types[item->inst_name] = item->inst_module;
    if (auto values = TryConstEvalInstParams(item)) {
      tables.interface_inst_param_values[item->inst_name] = std::move(*values);
    }
  }
  if (child->decl_kind == ModuleDeclKind::kChecker) {
    tables.checker_inst_names.insert(item->inst_name);
  }
  if (child->decl_kind == ModuleDeclKind::kProgram) {
    tables.program_inst_names.insert(item->inst_name);
  }
}

// Emits the parent-scope legality diagnostics for a module-instance item whose
// resolved child is `child`: an interface may not instantiate a module, and a
// program or checker may only instantiate checkers.
void CheckModuleInstParentRules(const ModuleItem* item, const ModuleDecl* decl,
                                const ModuleDecl* child,
                                const ParentScopeKind& parent,
                                DiagEngine& diag) {
  if (decl->decl_kind == ModuleDeclKind::kInterface &&
      child->decl_kind == ModuleDeclKind::kModule) {
    diag.Error(item->loc,
               std::format("module '{}' cannot be instantiated inside "
                           "interface '{}'",
                           item->inst_module, decl->name));
  }
  if ((parent.is_program || parent.is_checker) &&
      child->decl_kind != ModuleDeclKind::kChecker) {
    diag.Error(item->loc,
               std::format("only checkers can be instantiated inside "
                           "{} '{}'",
                           parent.kind_word, decl->name));
  }
}

// Emits the per-item legality diagnostics that depend only on the parent decl
// kind (no instance resolution): forbidden primitives/nets/always/nested decls
// inside programs/checkers/interfaces, and records port-less nested programs.
void CheckProgramCheckerItemRules(
    const ModuleItem* item, const ModuleDecl* decl,
    const ParentScopeKind& parent,
    std::unordered_set<std::string_view>& program_inst_names,
    DiagEngine& diag) {
  if ((parent.is_program || parent.is_checker) &&
      item->kind == ModuleItemKind::kUdpInst) {
    diag.Error(item->loc, std::format("primitive cannot be instantiated inside "
                                      "{} '{}'",
                                      parent.kind_word, decl->name));
  }
  // §17.7: a checker body may define variables but not nets.
  if (parent.is_checker && item->kind == ModuleItemKind::kNetDecl) {
    diag.Error(item->loc,
               std::format("a net cannot be declared inside checker '{}'; "
                           "only variables may be defined in a checker body",
                           decl->name));
  }
  // Annex C.2.7: a general 'always' procedure is removed for checkers.
  if (parent.is_checker && item->kind == ModuleItemKind::kAlwaysBlock) {
    diag.Error(item->loc,
               std::format("a general 'always' procedure cannot be used "
                           "inside checker '{}'; use always_comb, "
                           "always_latch, or always_ff instead",
                           decl->name));
  }
  // §17.2: only further checkers may be declared inside a checker.
  if (parent.is_checker && item->kind == ModuleItemKind::kNestedModuleDecl &&
      item->nested_module_decl &&
      item->nested_module_decl->decl_kind != ModuleDeclKind::kChecker) {
    diag.Error(item->loc,
               std::format("a module, interface, or program cannot be "
                           "declared inside checker '{}'",
                           decl->name));
  }
  if (item->kind == ModuleItemKind::kNestedModuleDecl &&
      item->nested_module_decl &&
      item->nested_module_decl->decl_kind == ModuleDeclKind::kProgram &&
      item->nested_module_decl->ports.empty()) {
    program_inst_names.insert(item->nested_module_decl->name);
  }
  if (decl->decl_kind == ModuleDeclKind::kInterface &&
      item->kind == ModuleItemKind::kNestedModuleDecl &&
      item->nested_module_decl &&
      item->nested_module_decl->decl_kind == ModuleDeclKind::kModule) {
    diag.Error(item->loc,
               std::format("module '{}' cannot be declared inside "
                           "interface '{}'",
                           item->nested_module_decl->name, decl->name));
  }
}

// Returns true if a child instance named `name` already exists on the module,
// i.e. the nested module was explicitly instantiated by the source.
bool ModuleExplicitlyInstantiated(const RtlirModule* mod,
                                  std::string_view name) {
  for (const auto& child : mod->children) {
    if (child.module_name == name) return true;
  }
  return false;
}

// Indexes the nested module/interface/program declarations of `decl` by name
// and rejects a virtual-interface variable declared directly inside an
// interface body.
void CollectNestedModulesAndCheckVif(
    const ModuleDecl* decl,
    std::unordered_map<std::string_view, ModuleDecl*>& nested_module_decls,
    DiagEngine& diag) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl) {
      nested_module_decls[item->nested_module_decl->name] =
          item->nested_module_decl;
    }
    if (decl->decl_kind == ModuleDeclKind::kInterface &&
        item->kind == ModuleItemKind::kVarDecl &&
        item->data_type.kind == DataTypeKind::kVirtualInterface) {
      diag.Error(item->loc,
                 "virtual interface cannot be declared inside an interface");
    }
  }
}

// Records task names and indexes function declarations by name.
void RecordTaskFuncNames(
    const ModuleDecl* decl, std::unordered_set<std::string_view>& task_names,
    std::unordered_map<std::string_view, const ModuleItem*>& func_decls) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) {
      task_names.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl) {
      func_decls[item->name] = item;
    }
  }
}

// §6.21: a task/function with no explicit lifetime inherits the enclosing
// decl's lifetime (automatic if the decl is automatic, otherwise static).
void DefaultTaskFuncLifetimes(const ModuleDecl* decl) {
  for (auto* item : decl->items) {
    if ((item->kind == ModuleItemKind::kFunctionDecl ||
         item->kind == ModuleItemKind::kTaskDecl) &&
        !item->is_automatic && !item->is_static) {
      if (decl->is_automatic) {
        item->is_automatic = true;
      } else {
        item->is_static = true;
      }
    }
  }
}

// Collects the names of the automatic-lifetime tasks and functions.
void CollectAutoTaskFuncNames(
    const ModuleDecl* decl,
    std::unordered_set<std::string_view>& auto_task_func_names) {
  for (const auto* item : decl->items) {
    if ((item->kind == ModuleItemKind::kTaskDecl ||
         item->kind == ModuleItemKind::kFunctionDecl) &&
        item->is_automatic) {
      auto_task_func_names.insert(item->name);
    }
  }
}

// Records task and function declaration names, defaults their lifetime from the
// enclosing decl (§6.21), and collects the automatic ones. Mutates the three
// member tables passed by reference.
void ClassifyTaskFuncDecls(
    const ModuleDecl* decl, std::unordered_set<std::string_view>& task_names,
    std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    std::unordered_set<std::string_view>& auto_task_func_names) {
  RecordTaskFuncNames(decl, task_names, func_decls);
  DefaultTaskFuncLifetimes(decl);
  CollectAutoTaskFuncNames(decl, auto_task_func_names);
}

// §17.2/§17.7/§25.9: applies instance-classification and parent-scope legality
// rules to every item of `decl`; `find_child` resolves an instance's target.
template <typename FindChild>
void ClassifyAndCheckItems(const ModuleDecl* decl,
                           const ParentScopeKind& parent_scope,
                           InstClassTables& inst_class_tables, DiagEngine& diag,
                           FindChild&& find_child) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst) {
      const ModuleDecl* child = find_child(item->inst_module);
      if (child) {
        ClassifyInstantiatedChild(item, child, inst_class_tables);
        CheckModuleInstParentRules(item, decl, child, parent_scope, diag);
      }
    }
    CheckProgramCheckerItemRules(item, decl, parent_scope,
                                 inst_class_tables.program_inst_names, diag);
  }
}

// §16.12/§F.4.1: registers every property/sequence decl of `decl` into
// `registry` so a property may be referenced before its declaration.
void BuildPropertyRegistry(const ModuleDecl* decl, PropertyRegistry& registry) {
  registry = PropertyRegistry();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl ||
        item->kind == ModuleItemKind::kSequenceDecl) {
      registry.Register(item);
    }
  }
}

// True if port-less nested module `nested_decl` (named `name`) is an implicit-
// instantiation candidate: not an interface and not explicitly instantiated.
bool IsImplicitNestedInstantiationCandidate(std::string_view name,
                                            const ModuleDecl* nested_decl,
                                            const RtlirModule* mod) {
  if (!nested_decl->ports.empty()) return false;
  if (nested_decl->decl_kind == ModuleDeclKind::kInterface) return false;
  if (ModuleExplicitlyInstantiated(mod, name)) return false;
  return true;
}

}  // namespace

void Elaborator::RunPostItemValidations(const ModuleDecl* decl,
                                        RtlirModule* mod) {
  CheckAlwaysCombMultiDriver(decl, mod);
  ValidateModuleConstraints(decl, mod);
  ValidateValueParams(decl, mod);
  ValidateLhsPatternWidths(decl, mod);
  ValidateClockvarAccess(decl);
  ValidateCycleDelayDefaultClocking(decl);
  ValidateIntraAssignCycleDelay(decl);
  ValidateDuplicateDefaultClocking(decl);
  ValidateDefaultClockingReference(decl);
  ValidateDuplicateGlobalClocking(decl);
  ValidateGlobalClockReference(decl);
  ValidateContAssignToClockvar(decl);
  ValidatePrimitiveDriveToClockvar(decl);
  ValidateSyncDriveForm(decl);
  ValidateConstantFunctionCalls(decl);
  ValidateDpiOpenArrayArgs(decl);
  ValidateBackgroundFuncCallContext(decl);
  ValidateSequenceEventArgs(decl);
  ValidateHierRefIntoChecker(decl);
  ValidateHierRefIntoProgram(decl);
  ValidateProgramSubroutineCall(decl);
  ValidateHierRefToAutomatic(decl);
  ValidateHierRefToImportedName(decl, mod);
  ValidateUnresolvedReferences(decl, mod);
  ValidateHierRefInstanceArray(decl, mod);
  ValidateForwardTypedefsInScope(decl);
  ValidateForwardTypedefScopePrefix(decl);
}

void Elaborator::ElaborateItems(const ModuleDecl* decl, RtlirModule* mod) {
  ReclassifyForwardUdpInstances(decl);
  // §23.2.2.1: do NOT reset the per-module item-elaboration state here.
  // ElaborateModule already reset it via the ItemElaborationStateSaver before
  // ElaboratePorts ran, and ElaboratePorts populated the ANSI/non-ANSI
  // port-name tables (complete/partial/signed ports) that the body net and
  // variable declarations below reconcile against. Re-running the reset would
  // wipe those tables before reconciliation, silently dropping the
  // redeclaration, range-mismatch, and signedness checks.
  CollectNestedModulesAndCheckVif(decl, nested_module_decls_, diag_);
  const bool kParentIsProgram = decl->decl_kind == ModuleDeclKind::kProgram;
  const bool kParentIsChecker = decl->decl_kind == ModuleDeclKind::kChecker;
  const ParentScopeKind kParentScope{kParentIsProgram, kParentIsChecker,
                                     kParentIsProgram
                                         ? std::string_view{"program"}
                                         : std::string_view{"checker"}};
  InstClassTables inst_class_tables{interface_inst_types_,
                                    interface_inst_param_values_,
                                    checker_inst_names_, program_inst_names_};

  ClassifyAndCheckItems(
      decl, kParentScope, inst_class_tables, diag_,
      [&](std::string_view name) { return FindModuleInScope(name); });

  for (const auto& [pname, pval] : decl->params) {  // §6.20: params are consts.
    const_names_.insert(pname);
  }

  ClassifyTaskFuncDecls(decl, task_names_, func_decls_, auto_task_func_names_);

  std::vector<std::pair<std::string_view, ModuleDecl*>> local_nested_modules(
      nested_module_decls_.begin(), nested_module_decls_.end());

  BuildPropertyRegistry(decl, property_registry_);

  for (auto* item : decl->items) {
    ElaborateItem(item, mod);
  }

  for (const auto& [name, nested_decl] : local_nested_modules) {
    if (!IsImplicitNestedInstantiationCandidate(name, nested_decl, mod))
      continue;
    if (HasParamPortWithoutDefault(nested_decl)) continue;
    RtlirModuleInst inst;
    inst.module_name = name;
    inst.inst_name = name;
    ParamList empty_params;

    std::string saved_inst_path = current_inst_path_;
    if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
    current_inst_path_.append(name.data(), name.size());
    // §23.9/§24.3: a nested module/program/interface resolves names declared in
    // this enclosing scope, so hand its visible names to ElaborateModule.
    pending_enclosing_scope_ = CaptureCurrentScopeNames();
    has_pending_enclosing_scope_ = true;
    inst.resolved = ElaborateModule(nested_decl, empty_params);
    current_inst_path_ = std::move(saved_inst_path);
    mod->children.push_back(inst);
  }

  RunPostItemValidations(decl, mod);
}

}  // namespace delta
