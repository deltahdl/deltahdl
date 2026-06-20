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

void Elaborator::ElaborateParamDecl(ModuleItem* item, RtlirModule* mod) {
  bool is_type = item->data_type.kind == DataTypeKind::kVoid &&
                 item->typedef_type.kind != DataTypeKind::kImplicit;

  // §6.20.3: a data type parameter (parameter type) can only be set to a data
  // type. The parser marks a type parameter with a void data type; if such a
  // parameter received an ordinary value expression instead of a type, it has
  // been set to a non-type and must be rejected.
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind == DataTypeKind::kImplicit &&
      item->init_expr != nullptr) {
    diag_.Error(item->loc,
                std::format("type parameter '{}' can only be set to a data "
                            "type, not a value expression",
                            item->name));
  }

  // §6.20.3: a type parameter declared with a leading enum, struct, or union
  // keyword restricts its valid types; assigning a type that does not conform
  // to that basic data type is an error. Resolve the assigned type through any
  // typedef chain and flag only a definite kind mismatch, leaving an
  // unresolved named type alone.
  if (is_type && (item->forward_type_kind == DataTypeKind::kEnum ||
                  item->forward_type_kind == DataTypeKind::kStruct ||
                  item->forward_type_kind == DataTypeKind::kUnion)) {
    const DataType* resolved = &item->typedef_type;
    for (int hops = 0; hops < 8 && resolved->kind == DataTypeKind::kNamed;
         ++hops) {
      auto td = typedefs_.find(resolved->type_name);
      if (td == typedefs_.end()) break;
      resolved = &td->second;
    }
    if (resolved->kind != DataTypeKind::kNamed &&
        resolved->kind != item->forward_type_kind) {
      static const auto basic_name = [](DataTypeKind k) -> std::string_view {
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
      diag_.Error(
          item->loc,
          std::format("type parameter '{}' is assigned a type that does "
                      "not conform to the required {} kind",
                      item->name, basic_name(item->forward_type_kind)));
    }
  }

  if (is_type) {
    typedefs_[item->name] = item->typedef_type;
  }
  RtlirParamDecl pd;
  pd.name = item->name;
  pd.is_type_param = is_type;

  pd.is_localparam = item->is_localparam || mod->has_param_port_list;
  pd.default_value = item->init_expr;
  if (!is_type) {
    PopulateParamTypeInfo(pd, item->data_type);
    // §11.5.1: a bit-select or part-select of a real parameter is illegal.
    // A real parameter holds a single scalar value, so record it alongside
    // scalar variables; any select applied to it is then rejected.
    DataTypeKind pk = item->data_type.kind;
    if (pk == DataTypeKind::kReal || pk == DataTypeKind::kShortreal ||
        pk == DataTypeKind::kRealtime) {
      scalar_var_names_.insert(item->name);
    }
  }

  if (item->init_expr && item->init_expr->kind == ExprKind::kIdentifier &&
      item->init_expr->text == "$") {
    pd.is_unbounded = true;
  } else if (item->init_expr &&
             item->init_expr->kind == ExprKind::kIdentifier &&
             RefersToUnboundedParam(mod, item->init_expr->text)) {
    // §6.20.7: it is legal to assign a $ (unbounded) parameter to another
    // parameter; the assigned-to parameter is itself unbounded.
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
    auto val = ConstEvalInt(item->init_expr, scope);
    if (val) {
      pd.resolved_value = *val;
      pd.is_resolved = true;
    } else if (!is_type && ParamExpectsIntegerValue(pd, item->data_type)) {
      // §6.20.2: the real-to-integer conversion of §6.12.1 applies to
      // parameters, so an integer-typed parameter initialized from a real
      // constant rounds to the nearest integer (ties away from zero).
      if (auto rval = ConstEvalReal(item->init_expr, scope)) {
        pd.resolved_value = std::llround(*rval);
        pd.is_resolved = true;
      }
    }
  }
  mod->params.push_back(pd);

  const_names_.insert(item->name);
}

void Elaborator::ElaborateItem(ModuleItem* item, RtlirModule* mod) {
  switch (item->kind) {
    case ModuleItemKind::kNetDecl:
      ElaborateNetDecl(item, mod);
      break;
    case ModuleItemKind::kVarDecl:
      ElaborateVarDecl(item, mod);
      break;
    case ModuleItemKind::kContAssign:
      ElaborateContAssign(item, mod);
      break;
    case ModuleItemKind::kInitialBlock:
      AddProcess(RtlirProcessKind::kInitial, item, mod, arena_, diag_);
      break;
    case ModuleItemKind::kFinalBlock:
      AddProcess(RtlirProcessKind::kFinal, item, mod, arena_, diag_);
      break;
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
      AddProcess(MapAlwaysKind(item->always_kind), item, mod, arena_, diag_,
                 &func_decls_);
      break;
    case ModuleItemKind::kModuleInst:
      ElaborateModuleInst(item, mod);
      break;
    case ModuleItemKind::kParamDecl:
      ElaborateParamDecl(item, mod);
      break;
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
    case ModuleItemKind::kGenerateFor:
      pending_generates_.push_back({item, mod});
      break;
    case ModuleItemKind::kTypedef:
      ElaborateTypedef(item, mod);
      break;
    case ModuleItemKind::kNettypeDecl:
      ElaborateNettypeDecl(item, mod);
      break;
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:

      if (!item->name.empty() && !declared_names_.insert(item->name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'", item->name));
      }

      if (item->method_class.empty() &&
          (item->is_method_initial || item->is_method_extends ||
           item->is_method_final)) {
        diag_.Error(item->loc,
                    "dynamic_override_specifiers shall only be legal on "
                    "method declarations inside a non-interface class scope");
      }
      ValidateFunctionBody(item);
      ValidateFunctionArgDefaultsScope(item);
      mod->function_decls.push_back(item);
      break;
    case ModuleItemKind::kGateInst:

      if (!item->gate_inst_name.empty() && !item->gate_terminals.empty() &&
          item->gate_terminals[0] &&
          item->gate_terminals[0]->kind == ExprKind::kIdentifier &&
          item->gate_terminals[0]->text == item->gate_inst_name) {
        diag_.Error(item->loc,
                    std::format("gate instance name '{}' conflicts with its "
                                "output net",
                                item->gate_inst_name));
      }

      if (!item->gate_inst_name.empty() &&
          !declared_names_.insert(item->gate_inst_name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'", item->gate_inst_name));
      }

      // §6.10: an undeclared identifier used in a primitive instance's
      // terminal list is assumed to be an implicit scalar net of the default
      // net type, the same assumption made for a module instance's port
      // connections.
      for (auto* term : item->gate_terminals) {
        if (term && term->kind == ExprKind::kIdentifier)
          MaybeCreateImplicitNet(term->text, item->loc, mod);
      }

      if (item->inst_range_left && item->inst_range_right) {
        auto range_scope = BuildParamScope(mod);
        auto lhi = ConstEvalInt(item->inst_range_left, range_scope);
        auto rhi = ConstEvalInt(item->inst_range_right, range_scope);
        if (!lhi || !rhi) {
          diag_.Error(item->loc,
                      "gate or switch instance range bound is not a constant "
                      "expression");
        } else {
          uint32_t array_len = static_cast<uint32_t>(std::abs(*lhi - *rhi) + 1);
          for (auto* term : item->gate_terminals) {
            uint32_t w = LookupLhsWidth(term, mod);
            if (w == 0) continue;
            // §28.3.6: an interconnect port or interconnect net expression
            // connected to an instance array shall have a bit-length equal to
            // the instance-array length. Unlike an ordinary scalar terminal it
            // cannot be broadcast (width 1) across the instances.
            bool is_interconnect = term &&
                                   term->kind == ExprKind::kIdentifier &&
                                   interconnect_names_.count(term->text) != 0;
            if (is_interconnect) {
              if (w != array_len) {
                diag_.Error(
                    item->loc,
                    "interconnect terminal of a gate instance array "
                    "must have a bit-length equal to the instance-array "
                    "length");
                break;
              }
              continue;
            }
            if (w != 1 && w != array_len) {
              diag_.Error(item->loc,
                          "gate array terminal width does not match either "
                          "the per-instance port width or the instance-array "
                          "length");
              break;
            }
          }
        }
      }
      ValidateBidirectionalSwitchConnections(item, mod, diag_,
                                             nettype_canonical_);
      ValidatePrimitiveOutputTerminalWidths(item, mod, diag_);
      ElaborateGateInst(item, mod, arena_);
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      break;
    case ModuleItemKind::kUdpInst:

      if (!item->gate_inst_name.empty() &&
          !declared_names_.insert(item->gate_inst_name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'", item->gate_inst_name));
      }
      // §6.10: undeclared identifiers in a UDP instance's terminal list also
      // become implicit scalar nets of the default net type.
      for (auto* term : item->gate_terminals) {
        if (term && term->kind == ExprKind::kIdentifier)
          MaybeCreateImplicitNet(term->text, item->loc, mod);
      }
      ResolveInterconnectPrimitiveTerminals(item->gate_terminals, mod);
      break;
    case ModuleItemKind::kSpecparam:
      specparam_names_.insert(item->name);
      const_names_.insert(item->name);
      ElaborateSpecparam(item, mod);
      break;
    case ModuleItemKind::kAlias: {
      for (auto* net : item->alias_nets) {
        if (net && net->kind == ExprKind::kIdentifier) {
          MaybeCreateImplicitNet(net->text, item->loc, mod);
        }
      }
      ValidateAlias(item, mod);
      RtlirAlias alias;
      alias.nets = item->alias_nets;
      mod->aliases.push_back(alias);
      break;
    }
    case ModuleItemKind::kSequenceDecl:
      sequence_names_.insert(item->name);
      mod->sequence_decls.push_back(item);
      // §16.8: a cyclic dependency among named sequences is an error.
      // PropertyRegistry has all sequence decls registered before any item
      // is elaborated (see ElaborateModule), so this DFS sees the full
      // graph regardless of declaration order.
      if (property_registry_.HasCyclicSequenceDependency(item)) {
        diag_.Error(item->loc,
                    "cyclic dependency among named sequences involving \"" +
                        std::string(item->name) + "\" (§16.8)");
      }
      // §16.10: a name that is already a formal argument of the sequence
      // declaration may not be redeclared as a body-scope local variable.
      ValidateNoFormalShadowedByBodyLocal(item);
      ValidateClockingBlock(item, mod);
      break;
    case ModuleItemKind::kDefparam:
      break;
    case ModuleItemKind::kImportDecl: {
      RtlirImport imp;
      imp.package_name = item->import_item.package_name;
      imp.item_name = item->import_item.item_name;
      imp.is_wildcard = item->import_item.is_wildcard;
      mod->imports.push_back(imp);
      break;
    }
    case ModuleItemKind::kExportDecl:

      break;
    case ModuleItemKind::kPropertyDecl: {
      // §16.12: nesting of disable iff is forbidden, explicitly or through
      // property instantiations. The flattened count via §F.4.1's rewriter
      // catches both cases.
      int flat_disable_iff = property_registry_.FlattenedDisableIffCount(item);
      if (flat_disable_iff > 1) {
        diag_.Error(item->loc, "property \"" + std::string(item->name) +
                                   "\" nests disable iff clauses (§16.12)");
      }
      // §16.10: same formal-vs-body shadow rule applies to a property
      // declaration: a formal-argument name cannot be redeclared as a
      // body-scope local variable.
      ValidateNoFormalShadowedByBodyLocal(item);
      // §16.12.17 / §F.7: enforce the restrictions on recursive properties.
      ValidateRecursiveProperty(item);
      ValidateClockingBlock(item, mod);
      break;
    }
    case ModuleItemKind::kAssertProperty:
      // §16.4.3: a deferred immediate assertion (assert/assume/cover with #0
      // or final) written directly as a module item, outside any procedure, is
      // a static deferred assertion. It is treated as if it were the sole
      // statement of an always_comb procedure, so build that implicit process
      // here rather than routing it through the concurrent-assertion path. The
      // parser wraps every module-level deferred immediate form under the
      // kAssertProperty kind, distinguished by a deferred statement body.
      if (item->body && item->body->is_deferred) {
        AddProcess(RtlirProcessKind::kAlwaysComb, item, mod, arena_, diag_,
                   &func_decls_);
        break;
      }
      ValidateClockingBlock(item, mod);
      break;
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
    case ModuleItemKind::kRestrictProperty:
    case ModuleItemKind::kClockingBlock:
      ValidateClockingBlock(item, mod);
      break;
    case ModuleItemKind::kElabSystemTask:
      ValidateElabSystemTask(item, mod);
      break;
    case ModuleItemKind::kDpiImport:
      ValidateDpiImport(item);
      mod->let_decls.push_back(item);
      break;
    case ModuleItemKind::kLetDecl:
      ValidateLetDecl(item);
      mod->let_decls.push_back(item);
      break;
    case ModuleItemKind::kCovergroupDecl:
    case ModuleItemKind::kSpecifyBlock:
    case ModuleItemKind::kDpiExport:
      mod->let_decls.push_back(item);
      break;
    case ModuleItemKind::kDefaultDisableIff:
    case ModuleItemKind::kNestedModuleDecl:
      break;
    case ModuleItemKind::kClassDecl:
      if (item->class_decl) {
        class_names_.insert(item->class_decl->name);
        if (!item->class_decl->params.empty())
          parameterized_class_names_.insert(item->class_decl->name);
        mod->class_decls.push_back(item->class_decl);
      }
      break;
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

void Elaborator::ElaborateItems(const ModuleDecl* decl, RtlirModule* mod) {
  ReclassifyForwardUdpInstances(decl);

  forward_typedef_kinds_.clear();
  declared_names_.clear();
  net_names_.clear();
  cont_assign_targets_.clear();
  proc_assign_targets_.clear();
  var_types_.clear();
  var_array_info_.clear();
  specparam_names_.clear();
  enum_var_names_.clear();
  enum_member_names_.clear();
  const_names_.clear();
  class_var_names_.clear();
  class_var_types_.clear();
  var_init_names_.clear();
  output_port_targets_.clear();
  nettype_net_names_.clear();
  interconnect_names_.clear();
  scalar_var_names_.clear();
  var_named_types_.clear();
  alias_pairs_.clear();
  non_ansi_complete_ports_.clear();
  non_ansi_partial_ports_.clear();
  ansi_port_names_.clear();
  clocking_signals_.clear();
  interface_inst_types_.clear();
  vi_var_interface_types_.clear();
  vi_var_modports_.clear();
  vi_var_param_values_.clear();
  interface_inst_param_values_.clear();
  checker_inst_names_.clear();
  program_inst_names_.clear();
  auto_task_func_names_.clear();
  nested_module_decls_.clear();
  task_names_.clear();
  sequence_names_.clear();
  func_decls_.clear();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl) {
      nested_module_decls_[item->nested_module_decl->name] =
          item->nested_module_decl;
    }

    if (decl->decl_kind == ModuleDeclKind::kInterface &&
        item->kind == ModuleItemKind::kVarDecl &&
        item->data_type.kind == DataTypeKind::kVirtualInterface) {
      diag_.Error(item->loc,
                  "virtual interface cannot be declared inside an interface");
    }
  }
  const bool parent_is_program = decl->decl_kind == ModuleDeclKind::kProgram;
  const bool parent_is_checker = decl->decl_kind == ModuleDeclKind::kChecker;
  const std::string_view parent_kind_word = parent_is_program
                                                ? std::string_view{"program"}
                                                : std::string_view{"checker"};

  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kModuleInst) {
      auto* child = FindModuleInScope(item->inst_module);
      if (child && child->decl_kind == ModuleDeclKind::kInterface) {
        interface_inst_types_[item->inst_name] = item->inst_module;
        // §25.9: record explicit parameter overrides (when they evaluate to
        // constants) so a later virtual-interface assignment can confirm the
        // actual parameter values match.
        if (!item->inst_params.empty()) {
          std::vector<int64_t> values;
          bool all_const = true;
          for (const auto& param : item->inst_params) {
            const Expr* pexpr = param.second;
            if (pexpr == nullptr) {
              all_const = false;
              break;
            }
            auto v = ConstEvalInt(pexpr);
            if (!v) {
              all_const = false;
              break;
            }
            values.push_back(*v);
          }
          if (all_const) {
            interface_inst_param_values_[item->inst_name] = std::move(values);
          }
        }
      }
      if (child && child->decl_kind == ModuleDeclKind::kChecker) {
        checker_inst_names_.insert(item->inst_name);
      }
      if (child && child->decl_kind == ModuleDeclKind::kProgram) {
        program_inst_names_.insert(item->inst_name);
      }
      if (decl->decl_kind == ModuleDeclKind::kInterface && child &&
          child->decl_kind == ModuleDeclKind::kModule) {
        diag_.Error(item->loc,
                    std::format("module '{}' cannot be instantiated inside "
                                "interface '{}'",
                                item->inst_module, decl->name));
      }
      if ((parent_is_program || parent_is_checker) && child &&
          child->decl_kind != ModuleDeclKind::kChecker) {
        diag_.Error(item->loc,
                    std::format("only checkers can be instantiated inside "
                                "{} '{}'",
                                parent_kind_word, decl->name));
      }
    }
    if ((parent_is_program || parent_is_checker) &&
        item->kind == ModuleItemKind::kUdpInst) {
      diag_.Error(item->loc,
                  std::format("primitive cannot be instantiated inside "
                              "{} '{}'",
                              parent_kind_word, decl->name));
    }

    // §17.7: a checker body may define variables (the checker variables of
    // §17.2's checker_or_generate_item_declaration), but defining nets in the
    // checker body is illegal.
    if (parent_is_checker && item->kind == ModuleItemKind::kNetDecl) {
      diag_.Error(item->loc,
                  std::format("a net cannot be declared inside checker '{}'; "
                              "only variables may be defined in a checker body",
                              decl->name));
    }

    // Annex C.2.7: the general-purpose always procedure in checkers is
    // deprecated and removed in this version of the standard. The specialized
    // always_comb, always_latch, and always_ff procedures have been added for
    // checkers and cover every case a general always could express, so a plain
    // always inside a checker body is rejected.
    if (parent_is_checker && item->kind == ModuleItemKind::kAlwaysBlock) {
      diag_.Error(item->loc,
                  std::format("a general 'always' procedure cannot be used "
                              "inside checker '{}'; use always_comb, "
                              "always_latch, or always_ff instead",
                              decl->name));
    }

    // §17.2: modules, interfaces, and programs shall not be declared inside a
    // checker. Only further checker declarations are permitted here.
    if (parent_is_checker && item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind != ModuleDeclKind::kChecker) {
      diag_.Error(item->loc,
                  std::format("a module, interface, or program cannot be "
                              "declared inside checker '{}'",
                              decl->name));
    }

    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind == ModuleDeclKind::kProgram &&
        item->nested_module_decl->ports.empty()) {
      program_inst_names_.insert(item->nested_module_decl->name);
    }
    if (decl->decl_kind == ModuleDeclKind::kInterface &&
        item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind == ModuleDeclKind::kModule) {
      diag_.Error(item->loc,
                  std::format("module '{}' cannot be declared inside "
                              "interface '{}'",
                              item->nested_module_decl->name, decl->name));
    }
  }

  for (const auto& [pname, pval] : decl->params) {
    const_names_.insert(pname);
  }

  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kTaskDecl) {
      task_names_.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kFunctionDecl) {
      func_decls_[item->name] = item;
    }
  }

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

  for (const auto* item : decl->items) {
    if ((item->kind == ModuleItemKind::kTaskDecl ||
         item->kind == ModuleItemKind::kFunctionDecl) &&
        item->is_automatic) {
      auto_task_func_names_.insert(item->name);
    }
  }

  std::vector<std::pair<std::string_view, ModuleDecl*>> local_nested_modules(
      nested_module_decls_.begin(), nested_module_decls_.end());

  // §16.12 lets a property be instantiated before its declaration, and
  // §F.4.1 assumes names are resolved before the rewriter runs. Build the
  // property/sequence registry up-front so flatten works for any decl.
  property_registry_ = PropertyRegistry();
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl ||
        item->kind == ModuleItemKind::kSequenceDecl) {
      property_registry_.Register(item);
    }
  }

  for (auto* item : decl->items) {
    ElaborateItem(item, mod);
  }

  for (const auto& [name, nested_decl] : local_nested_modules) {
    if (!nested_decl->ports.empty()) continue;
    if (nested_decl->decl_kind == ModuleDeclKind::kInterface) continue;

    if (HasParamPortWithoutDefault(nested_decl)) continue;
    bool explicitly_instantiated = false;
    for (const auto& child : mod->children) {
      if (child.module_name == name) {
        explicitly_instantiated = true;
        break;
      }
    }
    if (explicitly_instantiated) continue;
    RtlirModuleInst inst;
    inst.module_name = name;
    inst.inst_name = name;
    ParamList empty_params;

    std::string saved_inst_path = current_inst_path_;
    if (!current_inst_path_.empty()) current_inst_path_.push_back('.');
    current_inst_path_.append(name.data(), name.size());
    inst.resolved = ElaborateModule(nested_decl, empty_params);
    current_inst_path_ = std::move(saved_inst_path);
    mod->children.push_back(inst);
  }

  CheckAlwaysCombMultiDriver(decl, mod);
  ValidateModuleConstraints(decl);
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
  ValidateHierRefInstanceArray(decl);
  ValidateForwardTypedefsInScope(decl);
  ValidateForwardTypedefScopePrefix(decl);
}

ScopeMap Elaborator::BuildParamScope(const RtlirModule* mod) const {
  ScopeMap scope = cu_param_scope_;
  for (const auto& p : mod->params) {
    if (p.is_resolved) {
      scope[p.name] = p.resolved_value;
    }
  }
  return scope;
}

bool Elaborator::RefersToUnboundedParam(const RtlirModule* mod,
                                        std::string_view name) const {
  for (const auto& p : mod->params) {
    if (p.is_unbounded && p.name == name) return true;
  }
  return false;
}

bool Elaborator::ContainsDollarSubexpr(const Expr* e) const {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == "$") return true;
  if (ContainsDollarSubexpr(e->lhs)) return true;
  if (ContainsDollarSubexpr(e->rhs)) return true;
  if (ContainsDollarSubexpr(e->condition)) return true;
  if (ContainsDollarSubexpr(e->true_expr)) return true;
  if (ContainsDollarSubexpr(e->false_expr)) return true;
  if (ContainsDollarSubexpr(e->base)) return true;
  if (ContainsDollarSubexpr(e->index)) return true;
  if (ContainsDollarSubexpr(e->index_end)) return true;
  if (ContainsDollarSubexpr(e->with_expr)) return true;
  if (ContainsDollarSubexpr(e->repeat_count)) return true;
  for (const Expr* a : e->args)
    if (ContainsDollarSubexpr(a)) return true;
  for (const Expr* el : e->elements)
    if (ContainsDollarSubexpr(el)) return true;
  return false;
}

std::string_view Elaborator::ScopedName(std::string_view base) {
  if (gen_prefix_.empty()) return base;
  std::string full = gen_prefix_ + std::string(base);
  return {arena_.AllocString(full.c_str(), full.size()), full.size()};
}

}  // namespace delta
