#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_io_decl.h"
#include "elaborator/type_eval.h"
#include "elaborator/uwire_drivers.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static void CheckDuplicateExplicitPortNames(const ModuleDecl* decl,
                                            DiagEngine& diag) {
  std::unordered_set<std::string_view> explicit_names;
  for (const auto& port : decl->ports) {
    if (port.is_explicit_named && !port.name.empty()) {
      if (!explicit_names.insert(port.name).second) {
        diag.Error(port.loc,
                   std::format("duplicate port name '.{}'", port.name),
                   Subclause("23.2.2.1"));
      }
    }
  }
}

static void CheckDuplicateAnsiPortNames(
    const ModuleDecl* decl,
    std::unordered_set<std::string_view>& ansi_port_names, DiagEngine& diag) {
  for (const auto& port : decl->ports) {
    if (!port.name.empty()) {
      if (!ansi_port_names.insert(port.name).second) {
        diag.Error(port.loc, std::format("duplicate port name '{}'", port.name),
                   Subclause("23.2.2.2"));
      }
    }
  }
}

static void CheckDuplicatePortNames(
    const ModuleDecl* decl,
    std::unordered_set<std::string_view>& ansi_port_names, DiagEngine& diag) {
  if (decl->is_non_ansi_ports) {
    CheckDuplicateExplicitPortNames(decl, diag);
  } else {
    CheckDuplicateAnsiPortNames(decl, ansi_port_names, diag);
  }
}

static void ValidatePortDefaultValue(const PortDecl& port, bool is_non_ansi,
                                     const TypedefMap& typedefs,
                                     DiagEngine& diag) {
  if (port.direction != Direction::kInput) {
    diag.Error(
        port.loc,
        std::format("default value on {} port '{}'; defaults are "
                    "only allowed on input ports",
                    port.direction == Direction::kInout ? "inout" : "ref",
                    port.name),
        Subclause("23.2.2.4"));
  }
  if (is_non_ansi) {
    diag.Error(port.loc,
               std::format("default value on port '{}'; defaults are "
                           "only allowed with ANSI-style port "
                           "declarations",
                           port.name),
               Subclause("23.2.2.4"));
  }
  if (port.data_type.is_interconnect) {
    diag.Error(
        port.loc,
        std::format("default value on interconnect port '{}'", port.name),
        Subclause("23.2.2.4"));
  }
  if (!port.unpacked_dims.empty() ||
      !IsSingularType(port.data_type, typedefs)) {
    diag.Error(
        port.loc,
        std::format("default value on non-singular port '{}'", port.name),
        Subclause("23.2.2.4"));
  }
}

static void ValidatePortAssignment(const PortDecl& port, bool port_is_var,
                                   bool is_non_ansi, const TypedefMap& typedefs,
                                   DiagEngine& diag) {
  if (port.direction != Direction::kOutput) {
    ValidatePortDefaultValue(port, is_non_ansi, typedefs, diag);
    return;
  }
  if (port_is_var) return;
  diag.Error(port.loc,
             std::format("initializer on output port '{}', which is a net and "
                         "no variable; only a variable output port may be "
                         "initialized",
                         port.name),
             Subclause("23.2.2.2"));
}

static void ComputePortUnpackedDims(const PortDecl& port, RtlirPort& rp,
                                    const ScopeMap& scope,
                                    const TypeShapeTables& shapes,
                                    DiagEngine& diag) {
  for (auto* dim : port.unpacked_dims) {
    if (!IsFixedSizeUnpackedDim(dim, shapes)) continue;
    auto folded = FoldUnpackedDimBounds(dim, scope);
    if (!folded) {
      diag.Error(port.loc,
                 std::format("unpacked dimension of port '{}' is not a "
                             "constant expression",
                             port.name),
                 Subclause("7.4.2"));
      continue;
    }
    rp.unpacked_dims.push_back(*folded);
    rp.unpacked_dim_sizes.push_back(folded->Size());
  }
  rp.num_unpacked_dims = static_cast<uint32_t>(port.unpacked_dims.size());
}

static bool RejectIllegalPortType(const PortDecl& port, DiagEngine& diag) {
  if (port.data_type.kind == DataTypeKind::kChandle) {
    diag.Error(port.loc, "chandle cannot be used as a port type",
               Subclause("6.14"));
    return true;
  }
  if (port.data_type.kind == DataTypeKind::kVirtualInterface) {
    diag.Error(port.loc, "virtual interface cannot be used as a port type",
               Subclause("25.9"));
    return true;
  }
  return false;
}

static void DiagnoseMissingNonAnsiPortDirection(const PortDecl& port,
                                                bool is_non_ansi,
                                                DiagEngine& diag) {
  if (is_non_ansi && !port.name.empty() && !port.is_explicit_named &&
      port.direction == Direction::kNone) {
    diag.Error(port.loc,
               std::format("port '{}' has no direction declaration in the "
                           "module body",
                           port.name),
               Subclause("23.2.2.1"));
  }
}

static void DiagnosePortTypeConstraints(const PortDecl& port, bool port_is_var,
                                        DiagEngine& diag) {
  if (port.data_type.is_interconnect && port.data_type.is_signed) {
    diag.Error(port.loc,
               std::format("interconnect port '{}' shall not be declared "
                           "signed",
                           port.name),
               Subclause("23.2.2.3"));
  }
  if (port.direction == Direction::kInout && port_is_var) {
    diag.Error(port.loc,
               std::format("variable data type is not permitted on "
                           "inout port '{}'",
                           port.name),
               Subclause("23.3.3.2"));
  }
  if (port.direction == Direction::kRef && !port_is_var) {
    diag.Error(port.loc,
               std::format("ref port '{}' is declared with a net type; a ref "
                           "port is a variable",
                           port.name),
               Subclause("23.2.2.3"));
  }
}

static bool PortDataTypeIsJudgedByNetRules(const DataType& dtype) {
  return IsIntegralType(dtype.kind) || dtype.kind == DataTypeKind::kStruct ||
         dtype.kind == DataTypeKind::kUnion;
}

struct PortElabContext {
  const TypedefMap& typedefs;
  const ScopeMap& param_scope;
  std::unordered_set<std::string_view>& complete_ports;
  std::unordered_map<std::string_view, uint32_t>& partial_ports;
  std::unordered_set<std::string_view>& signed_ports;
  DiagEngine& diag;
  Arena& arena;
  RtlirModule* mod;
  const TypeShapeTables& shapes;
};

static const DataType* ResolvedPortAggregate(const ModuleDecl* decl,
                                             const PortDecl& port,
                                             const RtlirPort& rp,
                                             const PortElabContext& ctx) {
  if (decl->is_non_ansi_ports || decl->decl_kind == ModuleDeclKind::kChecker ||
      rp.is_interface_port || port.name.empty() || port.port_expr != nullptr ||
      !port.unpacked_dims.empty() ||
      port.data_type.packed_dim_left != nullptr ||
      !port.data_type.extra_packed_dims.empty()) {
    return nullptr;
  }
  return ResolvedAggregateType(port.data_type, ctx.typedefs, ctx.param_scope,
                               ctx.arena);
}

static void DeclareAggregatePortVariable(const PortDecl& port,
                                         const RtlirPort& rp,
                                         const DataType* aggregate,
                                         const PortElabContext& ctx) {
  RtlirVariable var;
  var.name = port.name;
  var.loc = port.loc;
  var.width = rp.width;
  var.is_4state = Is4stateType(port.data_type, ctx.typedefs);
  var.is_signed = IsSignedType(port.data_type, ctx.typedefs);
  var.init_expr = rp.init_value;
  var.elem_type_kind = port.data_type.kind;
  var.decl_kind = port.data_type.kind;
  var.dtype = aggregate;
  var.written_type = &port.data_type;
  ctx.mod->variables.push_back(var);
}

static void LayOutAggregatePort(const ModuleDecl* decl, const PortDecl& port,
                                RtlirPort& rp, const PortElabContext& ctx) {
  const DataType* aggregate = ResolvedPortAggregate(decl, port, rp, ctx);
  if (aggregate == nullptr) return;
  if (rp.is_var) {
    DeclareAggregatePortVariable(port, rp, aggregate, ctx);
    return;
  }
  rp.dtype = aggregate;
}

static void ValidateNetPortDataType(const ModuleDecl* decl,
                                    const PortDecl& port, bool port_is_var,
                                    const PortElabContext& ctx) {
  if (decl->decl_kind == ModuleDeclKind::kChecker) return;
  if (port_is_var) return;
  ValidateNetDataTypeIs4State(port.data_type, ctx.typedefs, ctx.diag, port.loc);
}

static void TrackNonAnsiPortType(const ModuleDecl* decl, const PortDecl& port,
                                 const PortElabContext& ctx) {
  if (!decl->is_non_ansi_ports || port.name.empty() ||
      port.direction == Direction::kNone) {
    return;
  }
  if (port.data_type.kind != DataTypeKind::kImplicit || port.has_explicit_var) {
    ctx.complete_ports.insert(port.name);
  } else {
    ctx.partial_ports[port.name] =
        EvalTypeWidth(port.data_type, ctx.typedefs, ctx.param_scope);
    if (port.data_type.is_signed) ctx.signed_ports.insert(port.name);
  }
}

static uint32_t SelectPortWidth(const Expr* expr, const ScopeMap& scope) {
  if (expr->kind != ExprKind::kSelect) return 0;
  if (expr->index_end == nullptr) return 1;
  if (expr->is_part_select_plus || expr->is_part_select_minus) {
    auto w = ConstEvalInt(expr->index_end, scope);
    return (w && *w > 0) ? static_cast<uint32_t>(*w) : 0;
  }
  auto left = ConstEvalInt(expr->index, scope);
  auto right = ConstEvalInt(expr->index_end, scope);
  if (!left || !right) return 0;
  return static_cast<uint32_t>(std::abs(*left - *right) + 1);
}

static RtlirPort BuildRtlirPortBase(const PortDecl& port, bool port_is_var,
                                    uint32_t width, const ScopeMap& scope,
                                    DiagEngine& diag) {
  RtlirPort rp;
  rp.name = port.name;
  rp.is_explicit_named = port.is_explicit_named;
  rp.attrs = ResolveAttributes(port.attrs, diag, scope);
  if (!port.is_explicit_named && port.port_expr != nullptr) rp.name = {};
  rp.direction = port.direction;
  rp.type_kind = port.data_type.kind;
  rp.declared_type = &port.data_type;
  rp.width = width;
  if (!port.is_explicit_named && port.port_expr != nullptr) {
    rp.port_expr = port.port_expr;
    if (uint32_t w = SelectPortWidth(port.port_expr, scope); w > 0) {
      rp.selected_width = width;
      rp.width = w;
    }
  }
  if (port.data_type.packed_dim_left != nullptr ||
      !port.data_type.extra_packed_dims.empty()) {
    rp.dtype = &port.data_type;
  }
  rp.is_signed = port.data_type.is_signed;
  rp.is_var = port_is_var;
  rp.is_interconnect = port.data_type.is_interconnect;
  if (!port_is_var) rp.net_type = WrittenNetType(port.data_type);
  if (port.direction == Direction::kOutput) {
    if (port_is_var) rp.init_value = port.default_value;
  } else {
    rp.default_value = port.default_value;
  }
  return rp;
}

static void ReportNonConstantPortSelects(const Expr* expr, SourceLoc loc,
                                         const ScopeMap& scope,
                                         DiagEngine& diag) {
  if (expr->kind == ExprKind::kConcatenation) {
    for (const Expr* each : expr->elements) {
      ReportNonConstantPortSelects(each, loc, scope, diag);
    }
    return;
  }
  for (; expr->kind == ExprKind::kSelect; expr = expr->base) {
    for (const Expr* bound : {expr->index, expr->index_end}) {
      if (bound != nullptr && !IsConstantExpr(bound, scope)) {
        diag.Error(loc,
                   "a port expression selects with an expression that is "
                   "not constant",
                   Subclause("A.1.3"));
      }
    }
  }
}

static RtlirPort ElaborateOnePort(const ModuleDecl* decl, const PortDecl& port,
                                  PortElabContext& ctx) {
  DiagnoseMissingNonAnsiPortDirection(port, decl->is_non_ansi_ports, ctx.diag);
  TrackNonAnsiPortType(decl, port, ctx);

  bool port_is_var =
      (!port.data_type.is_net && !port.data_type.is_interconnect) ||
      (decl->decl_kind == ModuleDeclKind::kChecker &&
       !PortDataTypeIsJudgedByNetRules(port.data_type));
  if (port.default_value) {
    ValidatePortAssignment(port, port_is_var, decl->is_non_ansi_ports,
                           ctx.typedefs, ctx.diag);
    if (decl->decl_kind != ModuleDeclKind::kChecker &&
        !IsConstantExpr(port.default_value, ctx.param_scope)) {
      ctx.diag.Error(port.loc,
                     std::format("default value of port '{}' is not a "
                                 "constant expression",
                                 port.name),
                     Subclause("23.2.2.4"));
    }
  }

  DiagnosePortTypeConstraints(port, port_is_var, ctx.diag);
  ValidateNetPortDataType(decl, port, port_is_var, ctx);
  if (decl->is_non_ansi_ports && port.port_expr != nullptr) {
    ReportNonConstantPortSelects(port.port_expr, port.loc, ctx.param_scope,
                                 ctx.diag);
  }

  uint32_t width = EvalTypeWidth(port.data_type, ctx.typedefs, ctx.param_scope);
  RtlirPort rp =
      BuildRtlirPortBase(port, port_is_var, width, ctx.param_scope, ctx.diag);
  ComputePortUnpackedDims(port, rp, ctx.param_scope, ctx.shapes, ctx.diag);
  rp.data_kind = ResolvedTypeKind(port.data_type, ctx.typedefs);
  if (decl->decl_kind != ModuleDeclKind::kChecker && !port_is_var &&
      !port.data_type.is_interconnect &&
      port.data_type.net_keyword == DataTypeKind::kImplicit &&
      DataTypeToNetType(port.data_type.kind) == NetType::kWire &&
      ctx.mod->default_nettype != NetType::kNone) {
    rp.net_type = ctx.mod->default_nettype;
  }
  return rp;
}

static void ValidateFixedSizePortDims(const ModuleDecl* decl,
                                      const PortDecl& port, const RtlirPort& rp,
                                      const PortElabContext& ctx) {
  if (decl->decl_kind == ModuleDeclKind::kChecker ||
      (rp.is_var && !rp.is_interface_port)) {
    return;
  }
  if (std::ranges::all_of(port.unpacked_dims, [&](const Expr* dim) {
        return IsFixedSizeUnpackedDim(dim, ctx.shapes);
      })) {
    return;
  }
  ctx.diag.Error(
      port.loc,
      std::format("{} port '{}' takes fixed-size unpacked "
                  "dimensions alone; a dynamic, associative or "
                  "queue dimension belongs to a variable port",
                  rp.is_interface_port ? "interface" : "net", port.name),
      Subclause(decl->is_non_ansi_ports ? "A.2.3" : "A.1.3"));
}

static void FoldPortConstant(Arena& arena, const ScopeMap& scope, bool is_real,
                             Expr*& value) {
  if (value == nullptr) return;
  if (value->kind == ExprKind::kIntegerLiteral ||
      value->kind == ExprKind::kStringLiteral) {
    return;
  }
  if (is_real) {
    auto r = ConstEvalReal(value, scope);
    if (!r) return;
    auto* lit = arena.Create<Expr>();
    lit->kind = ExprKind::kRealLiteral;
    lit->real_val = *r;
    value = lit;
    return;
  }
  auto v = ConstEvalInt(value, scope);
  if (!v) return;
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = static_cast<uint64_t>(*v);
  auto full = ConstEvalFull(value, scope);
  if (full && !full->high_words.empty()) {
    std::string text =
        std::format("{}'{}h", full->width, full->is_signed ? "s" : "");
    for (auto word = full->high_words.rbegin(); word != full->high_words.rend();
         ++word) {
      text += std::format("{:016x}", *word);
    }
    text += std::format("{:016x}", static_cast<uint64_t>(full->value));
    lit->text = std::string_view(arena.AllocString(text.data(), text.size()),
                                 text.size());
  }
  value = lit;
}

static void FoldPortDefaultValue(Arena& arena, const ScopeMap& scope,
                                 RtlirPort& rp) {
  bool is_real = rp.data_kind == DataTypeKind::kReal ||
                 rp.data_kind == DataTypeKind::kShortreal ||
                 rp.data_kind == DataTypeKind::kRealtime;
  FoldPortConstant(arena, scope, is_real, rp.default_value);
  FoldPortConstant(arena, scope, is_real, rp.init_value);
}

static void FoldBodyParamsIntoPortScope(const ModuleDecl* decl,
                                        ScopeMap& scope) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl ||
        item->init_expr == nullptr || item->name.empty()) {
      continue;
    }
    if (auto val = ConstEvalInt(item->init_expr, scope))
      scope[item->name] = *val;
  }
}

static bool BodyDeclaresObject(const ModuleDecl* decl, std::string_view name) {
  return std::any_of(decl->items.begin(), decl->items.end(),
                     [&](const ModuleItem* item) {
                       return (item->kind == ModuleItemKind::kNetDecl ||
                               item->kind == ModuleItemKind::kVarDecl) &&
                              item->name == name;
                     });
}

struct PortNetNameSets {
  std::unordered_set<std::string_view>& interconnects;
  std::unordered_set<std::string_view>& nets;
  UwireDrivers& uwire_drivers;
};

static void RegisterPortNetNames(const ModuleDecl* decl, const PortDecl& port,
                                 const RtlirPort& rp, PortNetNameSets sets) {
  if (port.name.empty()) return;
  if (port.data_type.is_interconnect) sets.interconnects.insert(port.name);
  if (decl->decl_kind == ModuleDeclKind::kChecker || rp.is_var) return;
  if (decl->is_non_ansi_ports && BodyDeclaresObject(decl, port.name)) return;
  sets.nets.insert(port.name);
  if (rp.net_type == NetType::kUwire) sets.uwire_drivers.Declare(port.name);
}

static void DeclarePortExprObjects(const ModuleDecl* decl, RtlirModule* mod,
                                   PortElabContext& ctx) {
  for (const PortDecl& obj : decl->port_expr_objects) {
    if (BodyDeclaresObject(decl, obj.name)) continue;
    RtlirPort rp = ElaborateOnePort(decl, obj, ctx);
    if (rp.net_type != NetType::kNone) {
      RtlirNet net;
      net.name = obj.name;
      net.loc = obj.loc;
      net.net_type = rp.net_type;
      net.width = rp.width;
      net.dtype = rp.dtype;
      net.is_signed = rp.is_signed;
      mod->nets.push_back(net);
      continue;
    }
    RtlirVariable var;
    var.name = obj.name;
    var.loc = obj.loc;
    var.width = rp.width;
    var.is_signed = rp.is_signed;
    var.is_4state = Is4stateType(obj.data_type, ctx.typedefs);
    var.dtype = rp.dtype;
    var.written_type = &obj.data_type;
    mod->variables.push_back(var);
  }
}

static Direction PortExprDirection(const ModuleDecl* decl, const Expr* expr) {
  while (expr != nullptr && expr->kind == ExprKind::kSelect) expr = expr->base;
  if (expr == nullptr) return Direction::kNone;
  if (expr->kind == ExprKind::kConcatenation) {
    return expr->elements.empty() ? Direction::kNone
                                  : PortExprDirection(decl, expr->elements[0]);
  }
  if (expr->kind != ExprKind::kIdentifier) return Direction::kNone;
  for (const PortDecl& obj : decl->port_expr_objects) {
    if (obj.name == expr->text) return obj.direction;
  }
  return Direction::kNone;
}

static void RecordPortExprDecls(const ModuleDecl* decl, RtlirModule* mod) {
  for (const PortDecl& obj : decl->port_expr_objects) {
    mod->port_expr_decls.push_back({obj.name, obj.direction, obj.name});
  }
  for (const PortDecl& port : decl->ports) {
    if (port.port_expr == nullptr || port.name.empty()) continue;
    if (!decl->is_non_ansi_ports) {
      const bool kNamesOne = port.port_expr->kind == ExprKind::kIdentifier;
      mod->port_expr_decls.push_back(
          {port.name, port.direction,
           kNamesOne ? port.port_expr->text : std::string_view{}});
      continue;
    }
    if (port.direction == Direction::kNone) continue;
    const bool kRecorded = std::ranges::any_of(
        mod->port_expr_decls,
        [&](const RtlirIoDecl& io) { return io.name == port.name; });
    if (!kRecorded) {
      mod->port_expr_decls.push_back({port.name, port.direction, port.name});
    }
  }
}

static bool PortTypeIsArray(
    const DataType& dtype, const TypedefMap& typedefs,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        typedef_dims) {
  if (dtype.packed_dim_left != nullptr) return true;
  std::vector<std::string_view> names;
  FollowTypedefs(dtype, typedefs, names);
  return std::ranges::any_of(names, [&](std::string_view name) {
    auto it = typedefs.find(name);
    return typedef_dims.contains(name) ||
           (it != typedefs.end() && it->second.packed_dim_left != nullptr);
  });
}

static void ResolvePortTypeRefs(
    const ModuleDecl* decl,
    const std::function<void(DataType&, SourceLoc)>& resolve, Arena& arena) {
  for (const auto& port : decl->ports) {
    resolve(const_cast<DataType&>(port.data_type), port.loc);
    ResolveTypeRefIndexDims(
        port.unpacked_dims, [&](DataType& type) { resolve(type, port.loc); },
        arena);
  }
}

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  auto param_scope = BuildParamScope(mod);
  FoldBodyParamsIntoPortScope(decl, param_scope);

  CheckDuplicatePortNames(decl, ansi_port_names_, diag_);

  const TypeShapeTables kShapes{typedefs_, td_array_dims_, class_names_};
  PortElabContext ctx{typedefs_,
                      param_scope,
                      non_ansi_complete_ports_,
                      non_ansi_partial_ports_,
                      non_ansi_signed_ports_,
                      diag_,
                      arena_,
                      mod,
                      kShapes};

  DeclarePortExprObjects(decl, mod, ctx);
  RecordPortExprDecls(decl, mod);
  ResolvePortTypeRefs(
      decl, [&](DataType& dt, SourceLoc loc) { ResolveTypeRef(dt, loc, mod); },
      arena_);
  for (const auto& port : decl->ports) {
    if (RejectIllegalPortType(port, diag_)) continue;

    RtlirPort rp = ElaborateOnePort(decl, port, ctx);
    if (port.port_expr != nullptr && rp.direction == Direction::kNone) {
      rp.direction = PortExprDirection(decl, port.port_expr);
    }
    RegisterPortNetNames(decl, port, rp,
                         {interconnect_names_, net_names_, uwire_drivers_});
    rp.loc = port.loc;
    {
      ParamRangeRegistryGuard registry(mod);
      FoldPortDefaultValue(arena_, param_scope, rp);
    }
    rp.elem_type_is_unpacked_array =
        port.data_type.kind == DataTypeKind::kNamed &&
        !port.unpacked_dims.empty() &&
        td_array_dims_.contains(port.data_type.type_name);
    rp.type_is_array =
        PortTypeIsArray(port.data_type, typedefs_, td_array_dims_);

    if (port.is_interface_port) {
      rp.is_interface_port = true;
      rp.interface_type_name = port.data_type.type_name;
    } else if (port.direction == Direction::kNone &&
               port.data_type.kind == DataTypeKind::kNamed &&
               !port.data_type.type_name.empty()) {
      auto* ifc_decl = FindModule(port.data_type.type_name);
      if (ifc_decl && ifc_decl->decl_kind == ModuleDeclKind::kInterface) {
        rp.is_interface_port = true;
        rp.interface_type_name = port.data_type.type_name;
      }
    }

    ValidateFixedSizePortDims(decl, port, rp, ctx);
    LayOutAggregatePort(decl, port, rp, ctx);
    mod->ports.push_back(rp);
  }
}

}  // namespace delta
