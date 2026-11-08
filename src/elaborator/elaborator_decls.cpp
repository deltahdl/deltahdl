#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_decls_internal.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/net_data_type.h"
#include "elaborator/queue_dim.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_element_shape.h"
#include "elaborator/type_eval.h"
#include "elaborator/uwire_drivers.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

namespace delta {

void InferDynArraySize(const std::vector<Expr*>& dims, const Expr* init,
                       RtlirVariable& var) {
  if (dims.empty() || dims[0] != nullptr) return;
  if (var.is_queue || var.is_assoc) return;
  var.is_dynamic = true;
  if (init && !init->elements.empty()) {
    var.unpacked_size = static_cast<uint32_t>(init->elements.size());
  }
}

static bool TryParseQueueDim(const Expr* dim, RtlirVariable& var,
                             DiagEngine& diag, SourceLoc loc,
                             const ScopeMap& scope) {
  if (!IsQueueDim(dim)) return false;
  var.is_queue = true;
  if (dim->rhs) {
    auto max_val = ConstEvalInt(dim->rhs, scope);
    if (max_val) {
      auto max_size = QueueBoundMaxSize(*max_val);
      if (max_size) {
        var.queue_max_size = *max_size;
      } else {
        diag.Error(loc, "queue bound must be a positive integer",
                   Subclause("7.10"));
      }
    }
  }
  return true;
}

static bool TryParseRangeDim(const Expr* dim, RtlirVariable& var,
                             const ScopeMap& scope) {
  if (dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon)
    return false;
  auto lval = ConstEvalInt(dim->lhs, scope);
  auto rval = ConstEvalInt(dim->rhs, scope);
  if (!lval || !rval) return false;
  auto lo = std::min(*lval, *rval);
  auto hi = std::max(*lval, *rval);
  var.unpacked_lo = lo;
  var.unpacked_size = static_cast<uint32_t>(hi - lo + 1);
  var.is_descending = (*lval > *rval);
  return true;
}

static uint32_t AssocIndexWidth(std::string_view t) {
  if (t == "bit" || t == "logic" || t == "reg") return 1;
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "longint" || t == "time" || t == "chandle" || t == "event") {
    return 64;
  }
  return 32;
}

static bool IsAssocIndexSigned(std::string_view t) {
  return t == "byte" || t == "shortint" || t == "int" || t == "integer" ||
         t == "longint";
}

static uint32_t AssocIndexWidth(const Expr* dim, const ScopeMap& scope) {
  if (dim->elements.empty()) return AssocIndexWidth(dim->text);
  uint32_t width = 1;
  for (const auto* packed_dim : dim->elements) {
    auto lval = ConstEvalInt(packed_dim->lhs, scope);
    auto rval = ConstEvalInt(packed_dim->rhs, scope);
    if (!lval || !rval) return AssocIndexWidth(dim->text);
    width *= static_cast<uint32_t>(std::abs(*lval - *rval) + 1);
  }
  return width;
}

static bool TryParseAssocDim(const Expr* dim, RtlirVariable& var,
                             const ScopeMap& scope) {
  if (dim->kind != ExprKind::kIdentifier) return false;
  auto t = dim->text;
  if (t == "string" || t == "int" || t == "integer" || t == "byte" ||
      t == "shortint" || t == "longint" || t == "bit" || t == "logic" ||
      t == "reg" || t == "time" || t == "chandle" || t == "event" || t == "*") {
    var.is_assoc = true;
    var.assoc_index_keyword = t;
    var.is_string_index = (t == "string");
    var.is_wildcard_index = (t == "*");
    var.assoc_index_width = AssocIndexWidth(dim, scope);
    var.is_index_signed = IsAssocIndexSigned(t);
    if (dim->op == TokenKind::kKwUnsigned) var.is_index_signed = false;
    if (dim->op == TokenKind::kKwSigned) var.is_index_signed = true;
    return true;
  }
  return false;
}

static bool IsUserDefinedType(
    std::string_view name, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  return typedefs.count(name) > 0 || class_names.count(name) > 0;
}

static void ApplyUserDefinedAssocDim(
    std::string_view name, RtlirVariable& var, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  var.is_assoc = true;
  if (class_names.count(name) > 0) {
    var.is_class_index = true;
    var.assoc_index_class_name = name;
    var.assoc_index_width = 64;
    return;
  }
  auto it = typedefs.find(name);
  if (it != typedefs.end()) {
    var.assoc_index_type_name = name;
    var.assoc_index_width = EvalTypeWidth(it->second, typedefs);
    var.is_index_signed = IsSignedType(it->second, typedefs);
  }
}

static void ApplyConstSizedUnpackedDim(const Expr* dim, RtlirVariable& var,
                                       DiagEngine& diag, SourceLoc loc,
                                       const ScopeMap& scope) {
  auto size_val = ConstEvalInt(dim, scope);
  if (!size_val) return;
  if (*size_val <= 0) {
    diag.Error(loc, "unpacked dimension size shall be a positive integer",
               Subclause("7.4.2"));
  } else {
    var.unpacked_size = static_cast<uint32_t>(*size_val);
  }
}

static std::string_view UserDefinedIndexName(
    const Expr* dim, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  if (dim->kind == ExprKind::kIdentifier) {
    return IsUserDefinedType(dim->text, typedefs, class_names)
               ? dim->text
               : std::string_view();
  }
  const std::string kKey = ScopedTypeKey(dim);
  if (auto td = typedefs.find(kKey); td != typedefs.end()) return td->first;
  auto cls = class_names.find(kKey);
  return cls == class_names.end() ? std::string_view() : *cls;
}

static bool TryParseUserDefinedAssocDim(
    const Expr* dim, RtlirVariable& var, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  const std::string_view kName =
      UserDefinedIndexName(dim, typedefs, class_names);
  if (kName.empty()) return false;
  ApplyUserDefinedAssocDim(kName, var, typedefs, class_names);
  return true;
}

static bool TryParseTypeRefAssocDim(const Expr* dim, RtlirVariable& var,
                                    const UnpackedDimContext& ctx) {
  if (dim->kind != ExprKind::kTypeRef || dim->type_value == nullptr) {
    return false;
  }
  const DataType& type = *dim->type_value;
  if (type.kind == DataTypeKind::kNamed) {
    ApplyUserDefinedAssocDim(type.type_name, var, ctx.types.typedefs,
                             ctx.types.class_names);
    return true;
  }
  var.is_assoc = true;
  var.is_string_index = type.kind == DataTypeKind::kString;
  var.assoc_index_width = EvalTypeWidth(type, ctx.types.typedefs, ctx.scope);
  var.is_index_signed = IsSignedType(type, ctx.types.typedefs);
  return true;
}

static bool TryParseAnyAssocDim(const Expr* dim, RtlirVariable& var,
                                const UnpackedDimContext& ctx) {
  return TryParseAssocDim(dim, var, ctx.scope) ||
         TryParseUserDefinedAssocDim(dim, var, ctx.types.typedefs,
                                     ctx.types.class_names) ||
         TryParseTypeRefAssocDim(dim, var, ctx);
}

static void RecordElementAssoc(const std::vector<Expr*>& dims,
                               RtlirVariable& var,
                               const UnpackedDimContext& ctx) {
  if (dims.size() != 2 || dims[1] == nullptr) return;
  RtlirVariable inner;
  if (!TryParseAnyAssocDim(dims[1], inner, ctx)) return;
  var.element.assoc_index = RtlirAssocIndex{
      inner.is_string_index,        inner.is_wildcard_index,
      inner.is_index_signed,        inner.assoc_index_width,
      inner.assoc_index_class_name, inner.assoc_index_type_name};
}

void ComputeUnpackedDims(const std::vector<Expr*>& dims, RtlirVariable& var,
                         const UnpackedDimContext& ctx) {
  if (dims.empty() || !dims[0]) return;
  auto* dim = dims[0];
  if (TryParseQueueDim(dim, var, ctx.diag, ctx.loc, ctx.scope)) return;
  if (TryParseAnyAssocDim(dim, var, ctx)) {
    RecordElementAssoc(dims, var, ctx);
    return;
  }
  if (TryParseRangeDim(dim, var, ctx.scope)) return;

  ApplyConstSizedUnpackedDim(dim, var, ctx.diag, ctx.loc, ctx.scope);
}

static void ValidateVectoredScalaredNet(const DataType& dtype,
                                        const RtlirNet& net, DiagEngine& diag,
                                        SourceLoc loc) {
  if ((dtype.is_vectored || dtype.is_scalared) && net.width <= 1 &&
      dtype.packed_dim_left == nullptr) {
    diag.Error(loc,
               "vectored or scalared requires at least one packed dimension",
               Subclause("6.9.2"));
  }
}

static void ValidateNetDriveStrength(const DataType& dtype, const RtlirNet& net,
                                     DiagEngine& diag, SourceLoc loc) {
  if (dtype.drive_strength0 == 0 && dtype.drive_strength1 == 0) return;
  if (net.net_type == NetType::kSupply0 || net.net_type == NetType::kSupply1) {
    diag.Error(loc,
               "drive strength on continuous assignment does not apply to "
               "supply0 or supply1 nets",
               Subclause("10.3.4"));
  } else if (net.width > 1) {
    diag.Error(loc,
               "drive strength on continuous assignment applies only to "
               "scalar nets",
               Subclause("10.3.4"));
  }
}

void ValidateDriveStrengthHasAssignment(const ModuleItem* item,
                                        DiagEngine& diag) {
  if ((item->data_type.drive_strength0 != 0 ||
       item->data_type.drive_strength1 != 0) &&
      item->init_expr == nullptr) {
    diag.Error(item->loc,
               "drive strength on net declaration requires an assignment",
               Subclause("6.3.2"));
  }
}

static RtlirContAssign BuildNetDeclContAssign(const ModuleItem* item,
                                              const RtlirNet& net,
                                              Arena& arena) {
  auto* lhs = arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = item->name;
  lhs->range = item->init_expr->range;
  RtlirContAssign ca;
  ca.lhs = lhs;
  ca.rhs = item->init_expr;
  ca.source_item = item;
  ca.width = net.width;
  ca.drive_strength0 = item->data_type.drive_strength0;
  ca.drive_strength1 = item->data_type.drive_strength1;
  ca.delay = item->net_delay;
  ca.delay_fall = item->net_delay_fall;
  ca.delay_decay = item->net_delay_decay;
  return ca;
}

struct NetDeclLowerSink {
  RtlirModule* mod;
  Arena& arena;
  std::unordered_map<std::string_view, SourceLoc>& cont_assign_targets;
  UwireDrivers& uwire_drivers;
};

static void LowerNetDeclAssignment(const ModuleItem* item, const RtlirNet& net,
                                   NetDeclLowerSink sink, DiagEngine& diag) {
  if (net.net_type == NetType::kUwire) sink.uwire_drivers.Declare(net.name);
  if (!item->init_expr) return;
  if (item->data_type.is_interconnect) {
    diag.Error(
        item->loc,
        "an interconnect net cannot be given a value where it is declared",
        Subclause("10.3.1"));
    return;
  }
  sink.cont_assign_targets.emplace(net.name, item->loc);
  if (net.net_type == NetType::kUwire)
    sink.uwire_drivers.Record(item->name, net.name, {}, item->loc, diag);
  sink.mod->assigns.push_back(BuildNetDeclContAssign(item, net, sink.arena));
}

struct TriregDefaults {
  uint32_t strength = 0;
  bool has_strength = false;
  uint64_t decay_ticks = 0;
  bool decay_infinite = true;
  bool decay_is_real = false;
  double decay_real = 0.0;
};

static void ApplyTriregDecayTime(const ModuleItem* item, RtlirNet& net,
                                 const TriregDefaults& defaults,
                                 const ScopeMap& scope, DiagEngine& diag) {
  if (item->net_delay_decay == nullptr) {
    if (!defaults.decay_infinite) {
      net.decay_ticks = defaults.decay_ticks;
      net.decay_is_real = defaults.decay_is_real;
      net.decay_real = defaults.decay_real;
      net.decays = true;
    }
    return;
  }
  auto decay_ticks = ConstEvalInt(item->net_delay_decay, scope);
  std::optional<double> decay_real;
  if (!decay_ticks) {
    if (auto real_ticks = ConstEvalReal(item->net_delay_decay, scope)) {
      decay_ticks = std::llround(*real_ticks);
      decay_real = real_ticks;
    }
  }
  if (!decay_ticks) {
    diag.Warning(item->net_delay_decay->range.start,
                 "trireg charge decay time does not fold to a constant, so the "
                 "net is left holding its charge",
                 Subclause("28.16.2.2"));
    return;
  }
  if (*decay_ticks < 0) return;
  net.decay_ticks = static_cast<uint64_t>(*decay_ticks);
  if (decay_real) {
    net.decay_is_real = true;
    net.decay_real = *decay_real;
  }
  net.decays = true;
}

static void ApplyTriregNetDefaults(const ModuleItem* item, RtlirNet& net,
                                   const TriregDefaults& defaults,
                                   const ScopeMap& scope, DiagEngine& diag) {
  if (net.net_type != NetType::kTrireg) return;
  if (item->data_type.charge_strength == 0 && defaults.has_strength) {
    net.trireg_capacitance = defaults.strength;
  }
  ApplyTriregDecayTime(item, net, defaults, scope, diag);
}

static void RecordNetDeclDelay(const ModuleItem* item, RtlirNet& net) {
  if (item->init_expr != nullptr) return;
  net.delay_rise = item->net_delay;
  net.delay_fall = item->net_delay_fall;
  if (net.net_type == NetType::kTrireg) return;
  net.delay_turnoff = item->net_delay_decay;
}

std::string_view LhsSignalName(const Expr* lhs) {
  if (lhs == nullptr || lhs->kind != ExprKind::kIdentifier) return {};
  return lhs->text;
}

FoundSignalDecl FindSignalDecl(std::string_view name, const RtlirModule* mod) {
  for (const auto& v : mod->variables) {
    if (v.name == name) {
      return {v.dtype, v.width, v.num_unpacked_dims != 0, v.is_signed};
    }
  }
  for (const auto& n : mod->nets) {
    if (n.name == name) {
      return {n.dtype, n.width, n.num_unpacked_dims != 0, n.is_signed};
    }
  }
  for (const auto& p : mod->ports) {
    if (p.name == name) {
      return {p.dtype, p.width, p.num_unpacked_dims != 0, p.is_signed};
    }
  }
  return {};
}

namespace {

int64_t RangeSpan(int64_t left, int64_t right) {
  return (left >= right ? left - right : right - left) + 1;
}

std::optional<int64_t> InnerPackedStride(const DataType& dt,
                                         const ScopeMap& scope) {
  int64_t stride = 1;
  for (const auto& [left, right] : dt.extra_packed_dims) {
    auto lo = ConstEvalInt(left, scope);
    auto hi = ConstEvalInt(right, scope);
    if (!lo || !hi) return std::nullopt;
    stride *= RangeSpan(*lo, *hi);
  }
  return stride;
}

}  // namespace

PackedRange SignalDeclaredRange(std::string_view name, const RtlirModule* mod,
                                const ScopeMap& scope) {
  FoundSignalDecl decl = FindSignalDecl(name, mod);
  PackedRange implicit = PackedRange::Implicit(decl.width);
  const DataType* dt = decl.dtype;
  if (!dt || !dt->packed_dim_left || !dt->packed_dim_right) return implicit;
  auto left = ConstEvalInt(dt->packed_dim_left, scope);
  auto right = ConstEvalInt(dt->packed_dim_right, scope);
  if (!left || !right) return implicit;
  if (*left < 0 || *right < 0) return implicit;
  std::optional<int64_t> stride = InnerPackedStride(*dt, scope);
  if (!stride || *stride > 1) return implicit;
  if (RangeSpan(*left, *right) != static_cast<int64_t>(decl.width)) {
    return implicit;
  }
  return {*left, *right};
}

static void ValidateNetDeclDataType(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& nettype_names,
    const TypeShapeTables& tables, DiagEngine& diag) {
  if (item->data_type.kind == DataTypeKind::kNamed &&
      nettype_names.count(NamedTypeKey(item->data_type)) != 0) {
    return;
  }
  ValidateNetDataTypeIs4State(item->data_type, tables.typedefs, diag,
                              item->loc);
  ValidateNetTypedefDims(item->data_type, tables, diag, item->loc);
}

void Elaborator::RecordNetArrayShape(ModuleItem* item, const RtlirNet& net,
                                     RtlirModule* mod) {
  RecordVarSelectShape(item, typedefs_, var_select_shapes_);
  if (item->unpacked_dims.empty()) return;
  RtlirVariable dims;
  dims.width = net.width;
  dims.is_signed = net.is_signed;
  ComputeUnpackedDims(
      item->unpacked_dims, dims,
      {{typedefs_, class_names_}, BuildParamScope(mod), diag_, item->loc});
  TrackVarArrayInfo(item, dims, BuildParamScope(mod), net_array_info_);
}

static void CarryNetArrayDims(
    std::string_view name,
    const std::unordered_map<std::string_view, Elaborator::VarArrayInfo>& infos,
    RtlirNet& net) {
  auto it = infos.find(name);
  if (it == infos.end()) return;
  net.num_unpacked_dims = it->second.num_unpacked_dims;
  net.unpacked_dim_sizes = it->second.dim_sizes;
  for (const auto& dim : it->second.declared_dims) {
    net.unpacked_dims.push_back(RtlirUnpackedDim{dim.left, dim.right});
  }
}

static const DataType* NetDeclaredType(const ModuleItem* item,
                                       const TypedefMap& typedefs,
                                       const ScopeMap& scope, Arena& arena) {
  if (item->data_type.packed_dim_left != nullptr ||
      !item->data_type.extra_packed_dims.empty()) {
    return &item->data_type;
  }
  if (!item->unpacked_dims.empty()) return nullptr;
  const DataType* aggregate =
      ResolvedAggregateType(item->data_type, typedefs, scope, arena);
  if (aggregate != nullptr) return aggregate;
  return NamedPackedVectorType(item->data_type, typedefs, arena);
}

static void RecordWrittenNetType(const ModuleItem& item, RtlirNet& net) {
  net.written_type = &item.data_type;
  net.declared_unpacked_dims = &item.unpacked_dims;
  net.has_declared_packed_dim = item.data_type.packed_dim_left != nullptr &&
                                item.data_type.kind != DataTypeKind::kEnum;
}

void Elaborator::ElaborateNetDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item->data_type, item->loc, mod);

  ResolveClassScopedDeclType(item->data_type, typedefs_, unit_);
  ReportUnresolvedClassScopedType(item->data_type, item->loc, typedefs_, unit_,
                                  diag_);
  CheckDeclRedeclaration(
      item, {item->data_type, typedefs_},
      {ansi_port_names_, non_ansi_complete_ports_, non_ansi_partial_ports_,
       declared_names_, ScopedName(item->name),
       DeclaresNetOrVariable(item->name)},
      "net", diag_);
  net_names_.insert(item->name);
  var_types_[item->name] = item->data_type.kind;
  if (item->unpacked_dims.empty()) {
    if (item->data_type.packed_dim_left)
      packed_array_vars_.insert(item->name);
    else if (DeclaresScalar(item->data_type, typedefs_))
      scalar_var_names_.insert(item->name);
  }
  RtlirNet net;
  net.name = ScopedName(item->name);
  net.loc = item->loc;

  if (item->data_type.is_interconnect) interconnect_names_.insert(item->name);
  net.net_type = WrittenNetType(item->data_type);
  net.width = EvalTypeWidth(item->data_type, typedefs_, BuildParamScope(mod));
  net.dtype = NetDeclaredType(item, typedefs_, BuildParamScope(mod), arena_);
  net.data_kind = ResolvedTypeKind(item->data_type, typedefs_);
  RecordWrittenNetType(*item, net);
  net.is_signed = IsSignedType(item->data_type, typedefs_);
  net.is_signed =
      ReconcilePartialPort(item->name, net.is_signed, net.net_type, mod);
  ValidatePackedDimRange(item->data_type, item->loc);

  const TypeShapeTables kShapeTables{typedefs_, td_array_dims_, class_names_};
  ValidateNetDeclDataType(item, nettype_names_, kShapeTables, diag_);
  ValidateNetDeclaratorDims(item->unpacked_dims, kShapeTables, diag_,
                            item->loc);

  if (item->data_type.charge_strength != 0 &&
      net.net_type != NetType::kTrireg) {
    diag_.Error(item->loc, "charge strength can only be used with trireg nets",
                Subclause("6.3.2.1"));
  }

  ValidateDriveStrengthHasAssignment(item, diag_);

  net.is_vectored = item->data_type.is_vectored;
  net.is_scalared = item->data_type.is_scalared;

  ValidateVectoredScalaredNet(item->data_type, net, diag_, item->loc);

  if (item->data_type.charge_strength != 0) {
    net.charge_strength =
        static_cast<Strength>(item->data_type.charge_strength);
  }

  ApplyTriregNetDefaults(
      item, net,
      TriregDefaults{
          mod->default_trireg_strength, mod->has_default_trireg_strength,
          mod->default_decay_time, mod->default_decay_time_infinite,
          mod->default_decay_time_is_real, mod->default_decay_time_real},
      BuildParamScope(mod), diag_);

  RecordNetDeclDelay(item, net);

  RecordNetArrayShape(item, net, mod);
  CarryNetArrayDims(item->name, net_array_info_, net);

  net.attrs = ResolveAttributes(item->attrs, diag_, BuildParamScope(mod));
  mod->nets.push_back(net);

  ValidateNetDriveStrength(item->data_type, net, diag_, item->loc);

  LowerNetDeclAssignment(
      item, net, {mod, arena_, cont_assign_targets_, uwire_drivers_}, diag_);
}

static void SetEnumTypeInfo(const ModuleItem* item, RtlirVariable& var,
                            const TypedefMap& typedefs, Arena& arena,
                            std::string_view& list_enum_key) {
  if (item->data_type.kind == DataTypeKind::kEnum) {
    if (item->first_in_decl_list) list_enum_key = item->name;
    var.enum_type_name = list_enum_key;
    var.dtype = &item->data_type;
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  const DataType* named = &item->data_type;
  const DataType* bound = FindNamedType(*named, typedefs);
  for (std::size_t steps = 0;
       bound != nullptr && bound->kind == DataTypeKind::kNamed &&
       steps < typedefs.size();
       ++steps) {
    named = bound;
    bound = FindNamedType(*named, typedefs);
  }
  if (bound != nullptr && bound->kind == DataTypeKind::kEnum) {
    var.enum_type_name =
        named->scope_name.empty()
            ? named->type_name
            : *arena.Create<std::string>(std::string(named->scope_name) +
                                         "::" + std::string(named->type_name));

    var.dtype = arena.Create<DataType>(*bound);
  }
}

static void SetStructTypeInfo(const ModuleItem* item, RtlirVariable& var,
                              const TypedefMap& typedefs, const ScopeMap& scope,
                              Arena& arena) {
  const DataType* aggregate =
      ResolvedAggregateType(item->data_type, typedefs, scope, arena);
  if (aggregate != nullptr) var.dtype = aggregate;
}

void Elaborator::SetVariableTypeInfo(const ModuleItem* item, RtlirVariable& var,
                                     const ScopeMap& scope) {
  SetStructTypeInfo(item, var, typedefs_, scope, arena_);
  std::string_view nested = NestedClassKey(item->data_type, unit_, arena_);
  if (nested.empty()) {
    nested = PackageClassKey(item->data_type, typedefs_, unit_, arena_);
  }
  if (!nested.empty()) {
    var.class_type_name = nested;
    var.class_data_type = &item->data_type;
  } else if (item->data_type.kind == DataTypeKind::kNamed &&
             class_names_.count(item->data_type.type_name)) {
    std::string_view type_name = item->data_type.type_name;
    bool std_sync = item->data_type.scope_name == "std" &&
                    (type_name == "semaphore" || type_name == "mailbox");
    var.class_type_name =
        std_sync ? *arena_.Create<std::string>("std::" + std::string(type_name))
                 : type_name;
    var.class_data_type = &item->data_type;
  }
  var.written_type = &item->data_type;
  SetEnumTypeInfo(item, var, typedefs_, arena_, inline_enum_list_key_);
  SetPackedTypedefTypeInfo(item, var, typedefs_, arena_);
  if (!var.dtype && (item->data_type.packed_dim_left != nullptr ||
                     !item->data_type.extra_packed_dims.empty())) {
    var.dtype = &item->data_type;
  }
}

void Elaborator::NameAdoptedArrayTypedef(const ModuleItem* item,
                                         std::string_view typedef_name,
                                         RtlirVariable& var) {
  if (typedef_name.empty()) return;
  var_named_types_[item->name] = typedef_name;
  if (item->data_type.kind == DataTypeKind::kEnum) {
    var.enum_type_name = typedef_name;
  }
}

}  // namespace delta
