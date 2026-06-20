#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <format>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

static NetType DataTypeToNetType(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kTri:
      return NetType::kTri;
    case DataTypeKind::kWand:
      return NetType::kWand;
    case DataTypeKind::kWor:
      return NetType::kWor;
    case DataTypeKind::kTriand:
      return NetType::kTriand;
    case DataTypeKind::kTrior:
      return NetType::kTrior;
    case DataTypeKind::kTri0:
      return NetType::kTri0;
    case DataTypeKind::kTri1:
      return NetType::kTri1;
    case DataTypeKind::kSupply0:
      return NetType::kSupply0;
    case DataTypeKind::kSupply1:
      return NetType::kSupply1;
    case DataTypeKind::kTrireg:
      return NetType::kTrireg;
    case DataTypeKind::kUwire:
      return NetType::kUwire;
    default:
      return NetType::kWire;
  }
}

static void InferDynArraySize(const std::vector<Expr*>& dims, const Expr* init,
                              RtlirVariable& var) {
  if (dims.empty() || dims[0] != nullptr) return;
  if (var.is_queue || var.is_assoc) return;
  var.is_dynamic = true;
  if (init && !init->elements.empty()) {
    var.unpacked_size = static_cast<uint32_t>(init->elements.size());
  }
}

static bool TryParseQueueDim(const Expr* dim, RtlirVariable& var,
                             DiagEngine& diag, SourceLoc loc) {
  if (dim->kind != ExprKind::kIdentifier || dim->text != "$") return false;
  var.is_queue = true;
  if (dim->rhs) {
    auto max_val = ConstEvalInt(dim->rhs);
    if (max_val) {
      if (*max_val <= 0) {
        diag.Error(loc, "queue bound must be a positive integer");
      } else {
        var.queue_max_size = static_cast<int32_t>(*max_val + 1);
      }
    }
  }
  return true;
}

static bool TryParseRangeDim(const Expr* dim, RtlirVariable& var) {
  if (dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon)
    return false;
  auto lval = ConstEvalInt(dim->lhs);
  auto rval = ConstEvalInt(dim->rhs);
  if (!lval || !rval) return false;
  auto lo = std::min(*lval, *rval);
  auto hi = std::max(*lval, *rval);
  var.unpacked_lo = static_cast<uint32_t>(lo);
  var.unpacked_size = static_cast<uint32_t>(hi - lo + 1);
  var.is_descending = (*lval > *rval);
  return true;
}

static uint32_t AssocIndexWidth(std::string_view t) {
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "longint") return 64;
  return 32;
}

static bool TryParseAssocDim(const Expr* dim, RtlirVariable& var) {
  if (dim->kind != ExprKind::kIdentifier) return false;
  auto t = dim->text;
  if (t == "string" || t == "int" || t == "integer" || t == "byte" ||
      t == "shortint" || t == "longint" || t == "*") {
    var.is_assoc = true;
    var.is_string_index = (t == "string");
    var.is_wildcard_index = (t == "*");
    var.assoc_index_width = AssocIndexWidth(t);
    // The built-in integral index types are signed; a wildcard index keeps an
    // unsigned, self-determined value (§7.8.4).
    var.is_index_signed = !var.is_wildcard_index;
    return true;
  }
  return false;
}

static bool IsUserDefinedType(
    std::string_view name, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  return typedefs.count(name) > 0 || class_names.count(name) > 0;
}

static void ComputeUnpackedDims(
    const std::vector<Expr*>& dims, RtlirVariable& var,
    const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names, DiagEngine& diag,
    SourceLoc loc) {
  if (dims.empty() || !dims[0]) return;
  auto* dim = dims[0];
  if (TryParseQueueDim(dim, var, diag, loc)) return;
  if (TryParseAssocDim(dim, var)) return;

  if (dim->kind == ExprKind::kIdentifier &&
      IsUserDefinedType(dim->text, typedefs, class_names)) {
    var.is_assoc = true;

    if (class_names.count(dim->text) > 0) {
      var.is_class_index = true;
      var.assoc_index_class_name = dim->text;
      var.assoc_index_width = 64;
    } else {
      auto it = typedefs.find(dim->text);
      if (it != typedefs.end()) {
        var.assoc_index_width = EvalTypeWidth(it->second, typedefs);
        // A typedef'd integral index follows the signedness of its underlying
        // type, so e.g. `bit signed [4:1]` orders signed and `bit [4:1]`
        // orders unsigned (§7.8.4).
        var.is_index_signed = IsSignedType(it->second, typedefs);
      }
    }
    return;
  }
  if (TryParseRangeDim(dim, var)) return;

  auto size_val = ConstEvalInt(dim);
  if (size_val) {
    if (*size_val <= 0) {
      diag.Error(loc, "unpacked dimension size shall be a positive integer");
    } else {
      var.unpacked_size = static_cast<uint32_t>(*size_val);
    }
  }
}

bool Elaborator::ReconcilePartialPortSignedness(std::string_view name,
                                                bool decl_signed,
                                                RtlirModule* mod) {
  // §23.2.2.1: the signed attribute may sit on the port direction declaration,
  // on the corresponding net/variable declaration, or on both; if either is
  // signed, the other is considered signed too.
  bool effective = decl_signed || non_ansi_signed_ports_.count(name) != 0;
  if (effective) {
    non_ansi_signed_ports_.insert(name);
    for (auto& p : mod->ports) {
      if (p.name == name) p.is_signed = true;
    }
  }
  return effective;
}

void Elaborator::ElaborateNetDecl(ModuleItem* item, RtlirModule* mod) {
  if (ansi_port_names_.count(item->name)) {
    diag_.Error(item->loc,
                std::format("redeclaration of ANSI port '{}'", item->name));
  }

  if (non_ansi_complete_ports_.count(item->name)) {
    diag_.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name));
  }

  auto it = non_ansi_partial_ports_.find(item->name);
  if (it != non_ansi_partial_ports_.end()) {
    uint32_t net_width = EvalTypeWidth(item->data_type, typedefs_);
    if (net_width != it->second) {
      diag_.Error(
          item->loc,
          std::format(
              "vector range of net '{}' does not match its port declaration",
              item->name));
    }
  } else if (!declared_names_.insert(item->name).second) {
    diag_.Error(item->loc, std::format("redeclaration of '{}'", item->name));
  }
  net_names_.insert(item->name);
  var_types_[item->name] = item->data_type.kind;
  if (!item->data_type.packed_dim_left)
    scalar_var_names_.insert(item->name);
  else if (item->unpacked_dims.empty())
    packed_array_vars_.insert(item->name);
  RtlirNet net;
  net.name = ScopedName(item->name);

  if (item->data_type.is_interconnect) {
    net.net_type = NetType::kInterconnect;
    interconnect_names_.insert(item->name);
  } else {
    net.net_type = DataTypeToNetType(item->data_type.kind);
  }
  net.width = EvalTypeWidth(item->data_type, typedefs_);
  net.is_signed = IsSignedType(item->data_type, typedefs_);
  if (non_ansi_partial_ports_.count(item->name)) {
    net.is_signed =
        ReconcilePartialPortSignedness(item->name, net.is_signed, mod);
  }
  ValidatePackedDimRange(item->data_type, item->loc);

  if (!item->data_type.is_interconnect) {
    DataTypeKind k = item->data_type.kind;
    if (k != DataTypeKind::kStruct && k != DataTypeKind::kUnion &&
        k != DataTypeKind::kEnum && k != DataTypeKind::kNamed &&
        DataTypeToNetType(k) == NetType::kWire && k != DataTypeKind::kWire &&
        !Is4stateType(k)) {
      diag_.Error(item->loc, "net data type must be 4-state");
    }
  }

  if (item->data_type.charge_strength != 0 &&
      net.net_type != NetType::kTrireg) {
    diag_.Error(item->loc, "charge strength can only be used with trireg nets");
  }
  net.is_vectored = item->data_type.is_vectored;
  net.is_scalared = item->data_type.is_scalared;

  if ((item->data_type.is_vectored || item->data_type.is_scalared) &&
      net.width <= 1 && item->data_type.packed_dim_left == nullptr) {
    diag_.Error(item->loc,
                "vectored or scalared requires at least one packed dimension");
  }

  if (item->data_type.charge_strength != 0) {
    net.charge_strength =
        static_cast<Strength>(item->data_type.charge_strength);
  }

  if (net.net_type == NetType::kTrireg &&
      item->data_type.charge_strength == 0 &&
      unit_->has_default_trireg_strength) {
    net.trireg_capacitance = unit_->default_trireg_strength;
  }
  if (item->net_delay_decay) {
    net.decay_ticks =
        static_cast<uint64_t>(ConstEvalInt(item->net_delay_decay).value_or(0));
  } else if (net.net_type == NetType::kTrireg &&
             !unit_->default_decay_time_infinite) {
    net.decay_ticks = unit_->default_decay_time;
  }

  net.attrs = ResolveAttributes(item->attrs, diag_);
  mod->nets.push_back(net);

  if ((item->data_type.drive_strength0 != 0 ||
       item->data_type.drive_strength1 != 0) &&
      net.width > 1 && net.net_type != NetType::kSupply0 &&
      net.net_type != NetType::kSupply1) {
    diag_.Error(item->loc,
                "drive strength on continuous assignment applies only to "
                "scalar nets");
  }

  if (item->init_expr) {
    if (item->data_type.is_interconnect) {
      diag_.Error(
          item->loc,
          "interconnect net shall not have a net declaration assignment");
      return;
    }
    auto* lhs = arena_.Create<Expr>();
    lhs->kind = ExprKind::kIdentifier;
    lhs->text = item->name;
    lhs->range = item->init_expr->range;
    cont_assign_targets_.emplace(item->name, item->loc);
    RtlirContAssign ca;
    ca.lhs = lhs;
    ca.rhs = item->init_expr;
    ca.width = net.width;
    ca.drive_strength0 = item->data_type.drive_strength0;
    ca.drive_strength1 = item->data_type.drive_strength1;
    ca.delay = item->net_delay;
    ca.delay_fall = item->net_delay_fall;
    ca.delay_decay = item->net_delay_decay;
    mod->assigns.push_back(ca);
  }
}

static void SetEnumTypeInfo(const ModuleItem* item, RtlirVariable& var,
                            const TypedefMap& typedefs, Arena& arena) {
  if (item->data_type.kind == DataTypeKind::kEnum) {
    var.enum_type_name = item->name;
    var.dtype = &item->data_type;
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto it = typedefs.find(item->data_type.type_name);
  if (it != typedefs.end() && it->second.kind == DataTypeKind::kEnum) {
    var.enum_type_name = item->data_type.type_name;

    var.dtype = arena.Create<DataType>(it->second);
  }
}

void Elaborator::SetStructTypeInfo(const ModuleItem* item, RtlirVariable& var) {
  if (item->data_type.kind == DataTypeKind::kStruct ||
      item->data_type.kind == DataTypeKind::kUnion) {
    var.dtype = &item->data_type;
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto td = typedefs_.find(item->data_type.type_name);
  if (td == typedefs_.end()) return;
  if (td->second.kind != DataTypeKind::kStruct &&
      td->second.kind != DataTypeKind::kUnion) {
    return;
  }

  var.dtype = arena_.Create<DataType>(td->second);
}

void Elaborator::ValidateVarDeclTypes(ModuleItem* item) {
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    class_var_names_.insert(item->name);
    class_var_types_[item->name] = item->data_type.type_name;

    if (item->data_type.type_params.empty()) {
      const auto* cls = FindClassDecl(item->data_type.type_name, unit_);
      if (cls && !cls->params.empty()) {
        for (const auto& [pname, pexpr] : cls->params) {
          if (!pexpr && !cls->type_param_names.count(pname)) {
            diag_.Error(item->loc,
                        std::format("parameterized class '{}' has no default "
                                    "specialization; parameter '{}' has no "
                                    "default value",
                                    cls->name, pname));
            break;
          }
        }
      }
    }

    if (item->data_type.type_name == "weak_reference" &&
        !item->data_type.type_params.empty()) {
      const auto& tp = item->data_type.type_params[0];
      if (tp.kind != DataTypeKind::kNamed ||
          !class_names_.count(tp.type_name)) {
        diag_.Error(item->loc,
                    "weak_reference type parameter shall be a class type");
      }
    }
  }
  if (item->data_type.kind == DataTypeKind::kEnum) {
    ValidateEnumDecl(item->data_type, item->loc);
  }
  if (item->data_type.kind == DataTypeKind::kStruct ||
      item->data_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->data_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->data_type, item->loc);
    ValidateStructMemberDefaultsConstant(item->data_type, item->loc);
    ValidateVoidMembers(item->data_type, item->loc);
    ValidateRandQualifiers(item->data_type, item->loc);
    ValidatePackedDimRequiresPackedKeyword(item->data_type, item->loc);
    ValidatePackedStructMemberTypes(item->data_type, item->loc);
    ValidateChandleInUnion(item->data_type, item->loc);
    ValidateVirtualInterfaceInUnion(item->data_type, item->loc);
    ValidatePackedUnion(item->data_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->data_type, item->loc);
  ValidatePackedDimOnDisallowedType(item->data_type, item->loc);
  ValidateAssocIndexType(item);
}

void Elaborator::TrackVarArrayInfo(const ModuleItem* item,
                                   const RtlirVariable& var) {
  if (item->unpacked_dims.empty()) return;
  VarArrayInfo info{item->data_type.kind,
                    var.unpacked_size,
                    static_cast<uint32_t>(item->unpacked_dims.size()),
                    var.width,
                    var.is_signed,
                    var.is_4state,
                    var.is_dynamic,
                    var.is_assoc,
                    {},
                    {}};
  info.is_queue = var.is_queue;
  if (var.is_assoc && item->unpacked_dims[0] &&
      item->unpacked_dims[0]->kind == ExprKind::kIdentifier) {
    info.assoc_index_type = item->unpacked_dims[0]->text;
  }
  for (auto* dim : item->unpacked_dims) {
    if (!dim) continue;
    if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      auto lv = ConstEvalInt(dim->lhs);
      auto rv = ConstEvalInt(dim->rhs);
      if (lv && rv) {
        info.dim_sizes.push_back(
            static_cast<uint32_t>(std::abs(*lv - *rv) + 1));
      }
    } else {
      auto sv = ConstEvalInt(dim);
      if (sv && *sv > 0) info.dim_sizes.push_back(static_cast<uint32_t>(*sv));
    }
  }
  var_array_info_[item->name] = info;
}

namespace {

// §25.9: leftmost identifier of a (possibly hierarchical) reference, e.g.
// "top" for the path top.u.sig.
std::string_view ReferenceRootName(const Expr* e) {
  while (e != nullptr) {
    if (e->kind == ExprKind::kIdentifier) return e->text;
    if (e->lhs != nullptr) {
      e = e->lhs;
    } else if (e->base != nullptr) {
      e = e->base;
    } else {
      break;
    }
  }
  return {};
}

// §25.9: a reference is "external" to an interface when it is a hierarchical
// (dotted or scope-qualified) reference whose root name is not declared
// within the interface body.
bool ExprRefsOutsideInterface(
    const Expr* e, const std::unordered_set<std::string_view>& local) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kMemberAccess) {
    auto root = ReferenceRootName(e);
    if (!root.empty() && local.find(root) == local.end()) return true;
  }
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty() &&
      local.find(e->text) == local.end()) {
    return true;
  }
  if (ExprRefsOutsideInterface(e->lhs, local)) return true;
  if (ExprRefsOutsideInterface(e->rhs, local)) return true;
  if (ExprRefsOutsideInterface(e->base, local)) return true;
  if (ExprRefsOutsideInterface(e->index, local)) return true;
  if (ExprRefsOutsideInterface(e->index_end, local)) return true;
  if (ExprRefsOutsideInterface(e->condition, local)) return true;
  if (ExprRefsOutsideInterface(e->true_expr, local)) return true;
  if (ExprRefsOutsideInterface(e->false_expr, local)) return true;
  if (ExprRefsOutsideInterface(e->repeat_count, local)) return true;
  for (const auto* a : e->args)
    if (ExprRefsOutsideInterface(a, local)) return true;
  for (const auto* el : e->elements)
    if (ExprRefsOutsideInterface(el, local)) return true;
  return false;
}

// §25.9: does the interface body reach outside itself through a hierarchical
// reference in a net/variable initializer or a continuous assignment?
bool InterfaceContainsExternalReference(const ModuleDecl* iface) {
  // §25.9: a port that references another interface also disqualifies the
  // interface from being used as a virtual interface type.
  for (const auto& p : iface->ports) {
    if (p.is_interface_port) return true;
  }
  std::unordered_set<std::string_view> local;
  for (const auto& p : iface->ports)
    if (!p.name.empty()) local.insert(p.name);
  for (const auto& param : iface->params)
    if (!param.first.empty()) local.insert(param.first);
  for (const auto* mp : iface->modports)
    if (mp && !mp->name.empty()) local.insert(mp->name);
  for (const auto* it : iface->items) {
    if (it == nullptr) continue;
    if (!it->name.empty()) local.insert(it->name);
    if (!it->inst_name.empty()) local.insert(it->inst_name);
  }
  for (const auto* it : iface->items) {
    if (it == nullptr) continue;
    if (ExprRefsOutsideInterface(it->init_expr, local)) return true;
    if (ExprRefsOutsideInterface(it->assign_lhs, local)) return true;
    if (ExprRefsOutsideInterface(it->assign_rhs, local)) return true;
  }
  return false;
}

}  // namespace

void Elaborator::ElaborateVarDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item, mod);

  ResolveParameterizedType(item->data_type);

  if (item->data_type.kind == DataTypeKind::kNamed &&
      nettype_names_.count(item->data_type.type_name)) {
    item->data_type.is_net = true;
    item->kind = ModuleItemKind::kNetDecl;
    nettype_net_names_.insert(item->name);
    ElaborateNetDecl(item, mod);

    auto& net = mod->nets.back();
    net.is_user_nettype = true;
    net.nettype_name = item->data_type.type_name;
    auto it = nettype_resolve_funcs_.find(item->data_type.type_name);
    if (it != nettype_resolve_funcs_.end()) {
      net.resolve_func = it->second;
    }
    return;
  }

  if (item->is_automatic) {
    diag_.Error(item->loc,
                "automatic lifetime is not allowed on module-level variables");
  }
  if (ansi_port_names_.count(item->name)) {
    diag_.Error(item->loc,
                std::format("redeclaration of ANSI port '{}'", item->name));
  }

  if (non_ansi_complete_ports_.count(item->name)) {
    diag_.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name));
  }

  auto partial_it = non_ansi_partial_ports_.find(item->name);
  if (partial_it != non_ansi_partial_ports_.end()) {
    uint32_t var_width = EvalTypeWidth(item->data_type, typedefs_);
    if (var_width != partial_it->second) {
      diag_.Error(
          item->loc,
          std::format("vector range of variable '{}' does not match its port "
                      "declaration",
                      item->name));
    }
  } else if (!declared_names_.insert(item->name).second) {
    diag_.Error(item->loc, std::format("redeclaration of '{}'", item->name));
  }

  if (item->data_type.is_const) {
    if (!item->init_expr) {
      diag_.Error(
          item->loc,
          std::format("const variable '{}' must be initialized", item->name));
    }
    const_names_.insert(item->name);
  }
  var_types_[item->name] = item->data_type.kind;
  if (!item->data_type.packed_dim_left)
    scalar_var_names_.insert(item->name);
  else if (item->unpacked_dims.empty())
    packed_array_vars_.insert(item->name);
  if (item->data_type.kind == DataTypeKind::kNamed)
    var_named_types_[item->name] = item->data_type.type_name;
  if (item->data_type.kind == DataTypeKind::kVirtualInterface) {
    auto iface_name = item->data_type.type_name;
    auto modport_name = item->data_type.modport_name;
    vi_var_interface_types_[item->name] = iface_name;
    vi_var_modports_[item->name] = modport_name;
    // §25.9: record explicit parameter overrides (when they evaluate to
    // constants) so a later assignment can confirm the actual parameter
    // values match the interface it is assigned from.
    if (!item->data_type.type_params.empty()) {
      std::vector<int64_t> values;
      bool all_const = true;
      for (const auto& tp : item->data_type.type_params) {
        if (tp.type_ref_expr == nullptr) {
          all_const = false;
          break;
        }
        auto v = ConstEvalInt(tp.type_ref_expr);
        if (!v) {
          all_const = false;
          break;
        }
        values.push_back(*v);
      }
      if (all_const) {
        vi_var_param_values_[item->name] = std::move(values);
      }
    }
    auto* iface_decl = FindModule(iface_name);
    if (!iface_decl || iface_decl->decl_kind != ModuleDeclKind::kInterface) {
      diag_.Error(item->loc,
                  std::format("unknown interface '{}' in virtual interface "
                              "declaration",
                              iface_name));
    } else if (!modport_name.empty()) {
      bool found = false;
      for (const auto* mp : iface_decl->modports) {
        if (mp && mp->name == modport_name) {
          found = true;
          break;
        }
      }
      if (!found) {
        diag_.Error(item->loc,
                    std::format("modport '{}' not found in interface '{}'",
                                modport_name, iface_name));
      }
    }
    // §25.9: an interface containing hierarchical references to objects
    // outside its body (or ports that reference other interfaces) shall not
    // be used as the type of a virtual interface.
    if (iface_decl && iface_decl->decl_kind == ModuleDeclKind::kInterface &&
        InterfaceContainsExternalReference(iface_decl)) {
      diag_.Error(item->loc,
                  std::format("interface '{}' contains references to objects "
                              "outside its body and cannot be used as a "
                              "virtual interface",
                              iface_name));
    }
  }
  RtlirVariable var;
  var.name = ScopedName(item->name);
  var.width = EvalTypeWidth(item->data_type, typedefs_);
  ValidatePackedDimRange(item->data_type, item->loc);
  var.is_4state = Is4stateType(item->data_type, typedefs_);
  var.is_event = (item->data_type.kind == DataTypeKind::kEvent);
  var.is_chandle = (item->data_type.kind == DataTypeKind::kChandle);
  var.is_string = (item->data_type.kind == DataTypeKind::kString);
  var.is_real = (item->data_type.kind == DataTypeKind::kReal ||
                 item->data_type.kind == DataTypeKind::kShortreal ||
                 item->data_type.kind == DataTypeKind::kRealtime);
  var.is_signed = IsSignedType(item->data_type, typedefs_);
  if (non_ansi_partial_ports_.count(item->name)) {
    var.is_signed =
        ReconcilePartialPortSignedness(item->name, var.is_signed, mod);
  }
  var.elem_type_kind = item->data_type.kind;
  var.init_expr = item->init_expr;

  if (item->init_expr) {
    var_init_names_.insert(item->name);
  }

  SetStructTypeInfo(item, var);

  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    var.class_type_name = item->data_type.type_name;
  }

  SetEnumTypeInfo(item, var, typedefs_, arena_);

  ComputeUnpackedDims(item->unpacked_dims, var, typedefs_, class_names_, diag_,
                      item->loc);
  ValidateUnpackedDimRange(item->unpacked_dims, item->loc);
  InferDynArraySize(item->unpacked_dims, item->init_expr, var);

  TrackVarArrayInfo(item, var);

  var.attrs = ResolveAttributes(item->attrs, diag_);
  mod->variables.push_back(var);
  ValidateArrayInitPattern(item);
  ValidateStructInitPattern(item);

  ValidateVarDeclTypes(item);
  TrackEnumVariable(item);
}

}  // namespace delta
