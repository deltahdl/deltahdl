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
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

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

static void ApplyUserDefinedAssocDim(
    const Expr* dim, RtlirVariable& var, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  var.is_assoc = true;
  if (class_names.count(dim->text) > 0) {
    var.is_class_index = true;
    var.assoc_index_class_name = dim->text;
    var.assoc_index_width = 64;
    return;
  }
  auto it = typedefs.find(dim->text);
  if (it != typedefs.end()) {
    var.assoc_index_width = EvalTypeWidth(it->second, typedefs);
    // A typedef'd integral index follows the signedness of its underlying
    // type, so e.g. `bit signed [4:1]` orders signed and `bit [4:1]`
    // orders unsigned (§7.8.4).
    var.is_index_signed = IsSignedType(it->second, typedefs);
  }
}

static void ApplyConstSizedUnpackedDim(const Expr* dim, RtlirVariable& var,
                                       DiagEngine& diag, SourceLoc loc) {
  auto size_val = ConstEvalInt(dim);
  if (!size_val) return;
  if (*size_val <= 0) {
    diag.Error(loc, "unpacked dimension size shall be a positive integer");
  } else {
    var.unpacked_size = static_cast<uint32_t>(*size_val);
  }
}

// §7.8: an identifier first dimension naming a typedef or class type makes the
// array associative with that user-defined index type. Returns true when the
// dimension was a user-defined associative index.
static bool TryParseUserDefinedAssocDim(
    const Expr* dim, RtlirVariable& var, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  if (dim->kind != ExprKind::kIdentifier ||
      !IsUserDefinedType(dim->text, typedefs, class_names)) {
    return false;
  }
  ApplyUserDefinedAssocDim(dim, var, typedefs, class_names);
  return true;
}

// §7.8: the set of user-defined type names an unpacked dimension may name as a
// user-defined associative index — the typedef table and the set of class
// names that together form the type-name resolution context.
struct TypeNameContext {
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
};

static void ComputeUnpackedDims(const std::vector<Expr*>& dims,
                                RtlirVariable& var,
                                const TypeNameContext& types, DiagEngine& diag,
                                SourceLoc loc) {
  if (dims.empty() || !dims[0]) return;
  auto* dim = dims[0];
  if (TryParseQueueDim(dim, var, diag, loc)) return;
  if (TryParseAssocDim(dim, var)) return;
  if (TryParseUserDefinedAssocDim(dim, var, types.typedefs, types.class_names))
    return;
  if (TryParseRangeDim(dim, var)) return;

  ApplyConstSizedUnpackedDim(dim, var, diag, loc);
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

// §23.2.2.1: bundle of name-table state that a net/variable declaration checks
// against (and updates) for redeclaration and partial-port reconciliation.
struct DeclNameTables {
  const std::unordered_set<std::string_view>& ansi_port_names;
  const std::unordered_set<std::string_view>& non_ansi_complete_ports;
  const std::unordered_map<std::string_view, uint32_t>& non_ansi_partial_ports;
  std::unordered_set<std::string_view>& declared_names;
  // §27.4: the declaration's generate-prefixed name, used as the redeclaration
  // key so distinct loop-iteration instances do not collide. Equals the bare
  // name for an unprefixed top-level declaration.
  std::string_view scoped_name;
};

// §23.2.2.1: diagnose redeclaration of a declared name against the ANSI and
// complete non-ANSI port name tables.
static void CheckPortNameRedeclaration(const ModuleItem* item,
                                       const DeclNameTables& tables,
                                       DiagEngine& diag) {
  if (tables.ansi_port_names.count(item->name)) {
    diag.Error(item->loc,
               std::format("redeclaration of ANSI port '{}'", item->name));
  }
  if (tables.non_ansi_complete_ports.count(item->name)) {
    diag.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name));
  }
}

// §23.2.2.1: the declared type whose vector width is reconciled against an
// earlier partial port declaration — the data type paired with the typedef
// table needed to evaluate its width.
struct DeclTypeRef {
  const DataType& dtype;
  const TypedefMap& typedefs;
};

// §23.2.2.1: reconcile a declaration against an earlier partial
// (direction-only) port declaration — width mismatch is an error — or, when
// there is no partial port, record the name and diagnose any plain
// redeclaration. `kind_word` selects "net" or "variable" in the vector-range
// message.
static void CheckPartialPortOrNameRedeclaration(const ModuleItem* item,
                                                const DeclTypeRef& decl_type,
                                                DeclNameTables tables,
                                                std::string_view kind_word,
                                                DiagEngine& diag) {
  auto it = tables.non_ansi_partial_ports.find(item->name);
  if (it != tables.non_ansi_partial_ports.end()) {
    uint32_t decl_width = EvalTypeWidth(decl_type.dtype, decl_type.typedefs);
    if (decl_width != it->second) {
      diag.Error(item->loc,
                 std::format("vector range of {} '{}' does not match its port "
                             "declaration",
                             kind_word, item->name));
    }
  } else if (!tables.declared_names.insert(tables.scoped_name).second) {
    // §27.4: each generate-loop iteration is a distinct block instance, so the
    // name is tracked under its generate-prefixed (scoped) form; an unprefixed
    // top-level declaration scopes to its bare name, leaving that case
    // unchanged. Only a true same-scope clash collides.
    diag.Error(item->loc, std::format("redeclaration of '{}'", item->name));
  }
}

// §23.2.2.1: diagnose redeclaration of a declared name and width mismatches
// against an earlier partial (direction-only) port declaration. `kind_word`
// selects "net" or "variable" in the vector-range message.
static void CheckDeclRedeclaration(const ModuleItem* item,
                                   const DeclTypeRef& decl_type,
                                   DeclNameTables tables,
                                   std::string_view kind_word,
                                   DiagEngine& diag) {
  CheckPortNameRedeclaration(item, tables, diag);
  CheckPartialPortOrNameRedeclaration(item, decl_type, tables, kind_word, diag);
}

// §6.7.1 / §23.2.2.1: a net declared with a vector type that cannot carry a
// 4-state value is rejected.
static void ValidateNetDataTypeIs4State(const DataType& dtype, DiagEngine& diag,
                                        SourceLoc loc) {
  if (dtype.is_interconnect) return;
  DataTypeKind k = dtype.kind;
  if (k != DataTypeKind::kStruct && k != DataTypeKind::kUnion &&
      k != DataTypeKind::kEnum && k != DataTypeKind::kNamed &&
      DataTypeToNetType(k) == NetType::kWire && k != DataTypeKind::kWire &&
      !Is4stateType(k)) {
    diag.Error(loc, "net data type must be 4-state");
  }
}

// §28.12: a vectored/scalared modifier requires at least one packed dimension.
static void ValidateVectoredScalaredNet(const DataType& dtype,
                                        const RtlirNet& net, DiagEngine& diag,
                                        SourceLoc loc) {
  if ((dtype.is_vectored || dtype.is_scalared) && net.width <= 1 &&
      dtype.packed_dim_left == nullptr) {
    diag.Error(loc,
               "vectored or scalared requires at least one packed dimension");
  }
}

// §10.3.1: drive strengths on a continuous assignment apply only to scalar
// nets (and never to supply nets).
static void ValidateNetDriveStrength(const DataType& dtype, const RtlirNet& net,
                                     DiagEngine& diag, SourceLoc loc) {
  if ((dtype.drive_strength0 != 0 || dtype.drive_strength1 != 0) &&
      net.width > 1 && net.net_type != NetType::kSupply0 &&
      net.net_type != NetType::kSupply1) {
    diag.Error(loc,
               "drive strength on continuous assignment applies only to "
               "scalar nets");
  }
}

// §6.10: build the continuous assignment that lowers a net declaration
// assignment — an identifier LHS naming the net driven by the initializer, with
// the net's width and the declaration's drive strengths and delays.
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
  ca.width = net.width;
  ca.drive_strength0 = item->data_type.drive_strength0;
  ca.drive_strength1 = item->data_type.drive_strength1;
  ca.delay = item->net_delay;
  ca.delay_fall = item->net_delay_fall;
  ca.delay_decay = item->net_delay_decay;
  return ca;
}

// §6.10: where a lowered net declaration assignment is emitted — the module
// receiving the continuous assignment, the arena that allocates its LHS, and
// the table recording continuous-assignment driver targets.
struct NetDeclLowerSink {
  RtlirModule* mod;
  Arena& arena;
  std::unordered_map<std::string_view, SourceLoc>& cont_assign_targets;
};

// §6.10: a net declaration assignment lowers to a continuous assignment of the
// initializer to the net (illegal on interconnect nets).
static void LowerNetDeclAssignment(const ModuleItem* item, const RtlirNet& net,
                                   NetDeclLowerSink sink, DiagEngine& diag) {
  if (!item->init_expr) return;
  if (item->data_type.is_interconnect) {
    diag.Error(item->loc,
               "interconnect net shall not have a net declaration assignment");
    return;
  }
  sink.cont_assign_targets.emplace(item->name, item->loc);
  sink.mod->assigns.push_back(BuildNetDeclContAssign(item, net, sink.arena));
}

// §6.10 / §28.16: apply the compilation unit's default trireg charge strength
// and decay-time settings to a freshly built trireg net.
static void ApplyTriregNetDefaults(const ModuleItem* item, RtlirNet& net,
                                   const CompilationUnit* unit) {
  if (net.net_type == NetType::kTrireg &&
      item->data_type.charge_strength == 0 &&
      unit->has_default_trireg_strength) {
    net.trireg_capacitance = unit->default_trireg_strength;
  }
  if (item->net_delay_decay) {
    net.decay_ticks =
        static_cast<uint64_t>(ConstEvalInt(item->net_delay_decay).value_or(0));
  } else if (net.net_type == NetType::kTrireg &&
             !unit->default_decay_time_infinite) {
    net.decay_ticks = unit->default_decay_time;
  }
}

void Elaborator::ElaborateNetDecl(ModuleItem* item, RtlirModule* mod) {
  // §6.23: a net declared with a type_reference data type (e.g. `wire type(x)
  // y`) resolves the referenced object's width/signedness before the net is
  // built.
  ResolveTypeRef(item, mod);
  CheckDeclRedeclaration(
      item, {item->data_type, typedefs_},
      {ansi_port_names_, non_ansi_complete_ports_, non_ansi_partial_ports_,
       declared_names_, ScopedName(item->name)},
      "net", diag_);
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

  ValidateNetDataTypeIs4State(item->data_type, diag_, item->loc);

  if (item->data_type.charge_strength != 0 &&
      net.net_type != NetType::kTrireg) {
    diag_.Error(item->loc, "charge strength can only be used with trireg nets");
  }
  net.is_vectored = item->data_type.is_vectored;
  net.is_scalared = item->data_type.is_scalared;

  ValidateVectoredScalaredNet(item->data_type, net, diag_, item->loc);

  if (item->data_type.charge_strength != 0) {
    net.charge_strength =
        static_cast<Strength>(item->data_type.charge_strength);
  }

  ApplyTriregNetDefaults(item, net, unit_);

  net.attrs = ResolveAttributes(item->attrs, diag_);
  mod->nets.push_back(net);

  ValidateNetDriveStrength(item->data_type, net, diag_, item->loc);

  LowerNetDeclAssignment(item, net, {mod, arena_, cont_assign_targets_}, diag_);
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

static void SetStructTypeInfo(const ModuleItem* item, RtlirVariable& var,
                              const TypedefMap& typedefs, Arena& arena) {
  if (item->data_type.kind == DataTypeKind::kStruct ||
      item->data_type.kind == DataTypeKind::kUnion) {
    auto* copy = arena.Create<DataType>(item->data_type);
    ResolveNestedAggregateTypes(*copy, typedefs, arena);
    var.dtype = copy;
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto td = typedefs.find(item->data_type.type_name);
  if (td == typedefs.end()) return;
  if (td->second.kind != DataTypeKind::kStruct &&
      td->second.kind != DataTypeKind::kUnion) {
    return;
  }

  auto* copy = arena.Create<DataType>(td->second);
  ResolveNestedAggregateTypes(*copy, typedefs, arena);
  var.dtype = copy;
}

// Records the declared-type information a variable carries beyond its raw
// width: struct/union layout, a class handle's type name, an enum's type, and —
// for a packed multidimensional array (§7.4.1, e.g. `logic [1:0][7:0]`) — the
// type itself so the lowerer can compute the outermost-element stride and a
// single-index select slices a whole element rather than one bit.
void Elaborator::SetVariableTypeInfo(const ModuleItem* item,
                                     RtlirVariable& var) {
  SetStructTypeInfo(item, var, typedefs_, arena_);
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    var.class_type_name = item->data_type.type_name;
  }
  SetEnumTypeInfo(item, var, typedefs_, arena_);
  if (!var.dtype && !item->data_type.extra_packed_dims.empty())
    var.dtype = &item->data_type;
}

static void ValidateParameterizedClassDefaults(const ModuleItem* item,
                                               const CompilationUnit* unit,
                                               DiagEngine& diag) {
  if (!item->data_type.type_params.empty()) return;
  const auto* cls = FindClassDecl(item->data_type.type_name, unit);
  if (!cls || cls->params.empty()) return;
  for (const auto& [pname, pexpr] : cls->params) {
    if (!pexpr && !cls->type_param_names.count(pname)) {
      diag.Error(item->loc,
                 std::format("parameterized class '{}' has no default "
                             "specialization; parameter '{}' has no "
                             "default value",
                             cls->name, pname));
      break;
    }
  }
}

static void ValidateWeakReferenceTypeParam(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& class_names, DiagEngine& diag) {
  if (item->data_type.type_name != "weak_reference" ||
      item->data_type.type_params.empty()) {
    return;
  }
  const auto& tp = item->data_type.type_params[0];
  if (tp.kind != DataTypeKind::kNamed || !class_names.count(tp.type_name)) {
    diag.Error(item->loc,
               "weak_reference type parameter shall be a class type");
  }
}

void Elaborator::ValidateVarDeclTypes(ModuleItem* item, const ScopeMap& scope) {
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    class_var_names_.insert(item->name);
    class_var_types_[item->name] = item->data_type.type_name;
    ValidateParameterizedClassDefaults(item, unit_, diag_);
    ValidateWeakReferenceTypeParam(item, class_names_, diag_);
  }
  if (item->data_type.kind == DataTypeKind::kEnum) {
    ValidateEnumDecl(item->data_type, item->loc);
  }
  if (item->data_type.kind == DataTypeKind::kStruct ||
      item->data_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->data_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->data_type, item->loc);
    ValidateStructMemberDefaultsConstant(item->data_type, item->loc, scope);
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

static void CollectUnpackedDimSizes(const std::vector<Expr*>& dims,
                                    std::vector<uint32_t>& dim_los,
                                    std::vector<uint32_t>& dim_sizes) {
  for (auto* dim : dims) {
    if (!dim) continue;
    if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
      auto lv = ConstEvalInt(dim->lhs);
      auto rv = ConstEvalInt(dim->rhs);
      if (!lv || !rv) continue;
      dim_los.push_back(static_cast<uint32_t>(std::min(*lv, *rv)));
      dim_sizes.push_back(static_cast<uint32_t>(std::abs(*lv - *rv) + 1));
    } else if (auto sv = ConstEvalInt(dim); sv && *sv > 0) {
      dim_los.push_back(0);
      dim_sizes.push_back(static_cast<uint32_t>(*sv));
    }
  }
}

void Elaborator::TrackVarArrayInfo(const ModuleItem* item, RtlirVariable& var) {
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
  std::vector<uint32_t> dim_los;
  CollectUnpackedDimSizes(item->unpacked_dims, dim_los, info.dim_sizes);
  var_array_info_[item->name] = info;
  // §7.4.2: carry full per-dimension extents to the simulator only when every
  // dimension is a fixed const size — queue/dynamic/assoc dims fall short of
  // the declared count, so the single-dimension unpacked_size/lo stays in
  // force.
  if (info.dim_sizes.size() >= 2 &&
      info.dim_sizes.size() == item->unpacked_dims.size()) {
    var.unpacked_dim_los = std::move(dim_los);
    var.unpacked_dim_sizes = info.dim_sizes;
  }
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
// §25.9: the node itself (ignoring children) is an external hierarchical
// reference — either a member access whose root is not local, or a
// scope-qualified identifier that is not local.
bool NodeIsExternalReference(
    const Expr* e, const std::unordered_set<std::string_view>& local) {
  if (e->kind == ExprKind::kMemberAccess) {
    auto root = ReferenceRootName(e);
    if (!root.empty() && local.find(root) == local.end()) return true;
  }
  if (e->kind == ExprKind::kIdentifier && !e->scope_prefix.empty() &&
      local.find(e->text) == local.end()) {
    return true;
  }
  return false;
}

bool ExprRefsOutsideInterface(
    const Expr* e, const std::unordered_set<std::string_view>& local);

// §25.9: recurse into the argument and element collections of a node.
bool ChildListRefsOutsideInterface(
    const Expr* e, const std::unordered_set<std::string_view>& local) {
  for (const auto* a : e->args)
    if (ExprRefsOutsideInterface(a, local)) return true;
  for (const auto* el : e->elements)
    if (ExprRefsOutsideInterface(el, local)) return true;
  return false;
}

bool ExprRefsOutsideInterface(
    const Expr* e, const std::unordered_set<std::string_view>& local) {
  if (e == nullptr) return false;
  if (NodeIsExternalReference(e, local)) return true;
  if (ExprRefsOutsideInterface(e->lhs, local)) return true;
  if (ExprRefsOutsideInterface(e->rhs, local)) return true;
  if (ExprRefsOutsideInterface(e->base, local)) return true;
  if (ExprRefsOutsideInterface(e->index, local)) return true;
  if (ExprRefsOutsideInterface(e->index_end, local)) return true;
  if (ExprRefsOutsideInterface(e->condition, local)) return true;
  if (ExprRefsOutsideInterface(e->true_expr, local)) return true;
  if (ExprRefsOutsideInterface(e->false_expr, local)) return true;
  if (ExprRefsOutsideInterface(e->repeat_count, local)) return true;
  if (ChildListRefsOutsideInterface(e, local)) return true;
  return false;
}

// §25.9: collect the port, parameter and modport names of an interface body.
void CollectInterfaceHeaderNames(const ModuleDecl* iface,
                                 std::unordered_set<std::string_view>& local) {
  for (const auto& p : iface->ports)
    if (!p.name.empty()) local.insert(p.name);
  for (const auto& param : iface->params)
    if (!param.first.empty()) local.insert(param.first);
  for (const auto* mp : iface->modports)
    if (mp && !mp->name.empty()) local.insert(mp->name);
}

// §25.9: collect the declared names and instance names of an interface's items.
void CollectInterfaceItemNames(const ModuleDecl* iface,
                               std::unordered_set<std::string_view>& local) {
  for (const auto* it : iface->items) {
    if (it == nullptr) continue;
    if (!it->name.empty()) local.insert(it->name);
    if (!it->inst_name.empty()) local.insert(it->inst_name);
  }
}

// §25.9: collect the names declared within an interface body (ports,
// parameters, modports, items and instance names) that count as "local".
std::unordered_set<std::string_view> CollectInterfaceLocalNames(
    const ModuleDecl* iface) {
  std::unordered_set<std::string_view> local;
  CollectInterfaceHeaderNames(iface, local);
  CollectInterfaceItemNames(iface, local);
  return local;
}

bool InterfaceContainsExternalReference(const ModuleDecl* iface) {
  // §25.9: a port that references another interface also disqualifies the
  // interface from being used as a virtual interface type.
  for (const auto& p : iface->ports) {
    if (p.is_interface_port) return true;
  }
  std::unordered_set<std::string_view> local =
      CollectInterfaceLocalNames(iface);
  for (const auto* it : iface->items) {
    if (it == nullptr) continue;
    if (ExprRefsOutsideInterface(it->init_expr, local)) return true;
    if (ExprRefsOutsideInterface(it->assign_lhs, local)) return true;
    if (ExprRefsOutsideInterface(it->assign_rhs, local)) return true;
  }
  return false;
}

// §25.9: record explicit parameter overrides of a virtual interface variable
// when they all evaluate to constants, so a later assignment can confirm the
// actual parameter values match the interface it is assigned from.
void RecordViParamOverrides(
    const ModuleItem* item,
    std::unordered_map<std::string_view, std::vector<int64_t>>& param_values) {
  if (item->data_type.type_params.empty()) return;
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
    param_values[item->name] = std::move(values);
  }
}

// §6.8 / §6.11: classify a scalar variable's element kind flags from its data
// type. Width/signedness/struct/enum info is filled in separately.
void SetVariableKindFlags(const ModuleItem* item, RtlirVariable& var,
                          const TypedefMap& typedefs) {
  var.is_4state = Is4stateType(item->data_type, typedefs);
  var.is_event = (item->data_type.kind == DataTypeKind::kEvent);
  var.is_chandle = (item->data_type.kind == DataTypeKind::kChandle);
  var.is_string = (item->data_type.kind == DataTypeKind::kString);
  var.is_real = (item->data_type.kind == DataTypeKind::kReal ||
                 item->data_type.kind == DataTypeKind::kShortreal ||
                 item->data_type.kind == DataTypeKind::kRealtime);
}

// §6.6.7: tag a net produced from a user-defined nettype with its nettype name
// and resolution function (if any).
void TagUserNettypeNet(
    const ModuleItem* item, RtlirNet& net,
    const std::unordered_map<std::string_view, std::string_view>&
        resolve_funcs) {
  net.is_user_nettype = true;
  net.nettype_name = item->data_type.type_name;
  auto it = resolve_funcs.find(item->data_type.type_name);
  if (it != resolve_funcs.end()) {
    net.resolve_func = it->second;
  }
}

// §25.9: validate that a virtual interface declaration names a real interface,
// a modport that exists on it, and an interface free of external references.
void ValidateVirtualInterfaceTarget(const ModuleItem* item,
                                    const ModuleDecl* iface_decl,
                                    std::string_view iface_name,
                                    std::string_view modport_name,
                                    DiagEngine& diag) {
  if (!iface_decl || iface_decl->decl_kind != ModuleDeclKind::kInterface) {
    diag.Error(item->loc,
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
      diag.Error(item->loc,
                 std::format("modport '{}' not found in interface '{}'",
                             modport_name, iface_name));
    }
  }
  // §25.9: an interface containing hierarchical references to objects outside
  // its body (or ports that reference other interfaces) shall not be used as
  // the type of a virtual interface.
  if (iface_decl && iface_decl->decl_kind == ModuleDeclKind::kInterface &&
      InterfaceContainsExternalReference(iface_decl)) {
    diag.Error(item->loc,
               std::format("interface '{}' contains references to objects "
                           "outside its body and cannot be used as a "
                           "virtual interface",
                           iface_name));
  }
}

}  // namespace

// §6.11 / §6.20 / §23.2.2.1: bundle of name-table state updated while
// registering a variable declaration's name (const-ness, kind, shape, named
// type).
struct VarDeclNameTables {
  std::unordered_set<std::string_view>& const_names;
  std::unordered_set<std::string_view>& const_var_names;
  std::unordered_map<std::string_view, DataTypeKind>& var_types;
  std::unordered_set<std::string_view>& scalar_var_names;
  std::unordered_set<std::string_view>& packed_array_vars;
  std::unordered_map<std::string_view, std::string_view>& var_named_types;
};

// §6.11.1 / Table 6-8: the integer atom types (byte, shortint, int, longint,
// integer, time) are multi-bit vector types with a fixed implicit width, not
// scalars. Per §11.5.1 a bit-select or part-select of a scalar is illegal, but
// these vector types are freely bit/part-selectable, so they must not be
// classified as scalars even though they carry no explicit packed dimension.
static bool IsIntegerAtomKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kInteger:
    case DataTypeKind::kLongint:
    case DataTypeKind::kTime:
      return true;
    default:
      return false;
  }
}

// §6.11 / §6.20: record the bookkeeping name tables for a variable declaration
// (const-ness, type kind, scalar/packed-array shape, named type) before the
// RtlirVariable is built.
static void RegisterVarDeclNames(const ModuleItem* item,
                                 VarDeclNameTables tables, DiagEngine& diag) {
  if (item->data_type.is_const) {
    if (!item->init_expr) {
      diag.Error(
          item->loc,
          std::format("const variable '{}' must be initialized", item->name));
    }
    tables.const_names.insert(item->name);
    tables.const_var_names.insert(item->name);
  }
  tables.var_types[item->name] = item->data_type.kind;
  // §7.4/§7.8: a variable carrying an unpacked dimension (fixed, dynamic,
  // queue, or associative array) is neither a scalar nor a packed-array
  // variable for select-legality purposes; indexing it is a legal array
  // select, not a bit-select of a scalar. Only dimensionless variables are
  // classified here.
  if (item->unpacked_dims.empty()) {
    if (item->data_type.packed_dim_left)
      tables.packed_array_vars.insert(item->name);
    else if (!IsIntegerAtomKind(item->data_type.kind))
      tables.scalar_var_names.insert(item->name);
  }
  if (item->data_type.kind == DataTypeKind::kNamed)
    tables.var_named_types[item->name] = item->data_type.type_name;
}

// §25.9: bundle of virtual-interface name-table state updated while registering
// a virtual interface variable declaration.
struct VirtualInterfaceVarTables {
  std::unordered_map<std::string_view, std::string_view>&
      vi_var_interface_types;
  std::unordered_map<std::string_view, std::string_view>& vi_var_modports;
  std::unordered_map<std::string_view, std::vector<int64_t>>&
      vi_var_param_values;
};

// §25.9: register a virtual interface variable's interface/modport bindings and
// validate the named interface target (`iface_decl` is the resolved interface,
// or null when unknown).
static void RegisterVirtualInterfaceVarDecl(const ModuleItem* item,
                                            const ModuleDecl* iface_decl,
                                            VirtualInterfaceVarTables tables,
                                            DiagEngine& diag) {
  if (item->data_type.kind != DataTypeKind::kVirtualInterface) return;
  auto iface_name = item->data_type.type_name;
  auto modport_name = item->data_type.modport_name;
  tables.vi_var_interface_types[item->name] = iface_name;
  tables.vi_var_modports[item->name] = modport_name;
  RecordViParamOverrides(item, tables.vi_var_param_values);
  ValidateVirtualInterfaceTarget(item, iface_decl, iface_name, modport_name,
                                 diag);
}

// §6.18 / §7.4 / §10.10.1: when a variable's named type is a fixed unpacked-
// array typedef and it declares no unpacked dimensions of its own, rewrite it
// to the typedef's element base type (keeping its own const-ness) plus the
// typedef's unpacked dimensions, so it elaborates and lowers identically to an
// inline unpacked-array declaration. Returns the adopted typedef name (empty
// when no rewrite happened) so the caller can keep the variable's named-type
// association, which the rewrite to a non-named base type would otherwise drop.
static std::string_view AdoptTypedefArrayDims(
    ModuleItem* item, const TypedefMap& typedefs,
    const std::unordered_map<std::string_view, std::vector<Expr*>>&
        td_array_dims) {
  if (!item->unpacked_dims.empty()) return {};
  if (item->data_type.kind != DataTypeKind::kNamed) return {};
  auto dims_it = td_array_dims.find(item->data_type.type_name);
  if (dims_it == td_array_dims.end()) return {};
  auto base_it = typedefs.find(item->data_type.type_name);
  if (base_it == typedefs.end()) return {};
  std::string_view typedef_name = item->data_type.type_name;
  bool was_const = item->data_type.is_const;
  item->data_type = base_it->second;
  item->data_type.is_const = was_const;
  item->unpacked_dims = dims_it->second;
  return typedef_name;
}

void Elaborator::ElaborateVarDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item, mod);

  ResolveParameterizedType(item->data_type);

  std::string_view adopted_array_typedef =
      AdoptTypedefArrayDims(item, typedefs_, td_array_dims_);

  if (item->data_type.kind == DataTypeKind::kNamed &&
      nettype_names_.count(item->data_type.type_name)) {
    item->data_type.is_net = true;
    item->kind = ModuleItemKind::kNetDecl;
    nettype_net_names_.insert(item->name);
    ElaborateNetDecl(item, mod);
    TagUserNettypeNet(item, mod->nets.back(), nettype_resolve_funcs_);
    return;
  }

  if (item->is_automatic) {
    diag_.Error(item->loc,
                "automatic lifetime is not allowed on module-level variables");
  }
  CheckDeclRedeclaration(
      item, {item->data_type, typedefs_},
      {ansi_port_names_, non_ansi_complete_ports_, non_ansi_partial_ports_,
       declared_names_, ScopedName(item->name)},
      "variable", diag_);

  RegisterVarDeclNames(
      item,
      {const_names_, const_var_names_, var_types_, scalar_var_names_,
       packed_array_vars_, var_named_types_},
      diag_);
  // §10.10.1 / §11.2.2: keep the named-type association for a variable that
  // adopted a typedef array's dimensions above; rewriting it to a non-named
  // base type kept RegisterVarDeclNames from recording it, but aggregate
  // type-equivalence checks still need to know its declared array typedef.
  if (!adopted_array_typedef.empty()) {
    var_named_types_[item->name] = adopted_array_typedef;
  }
  const ModuleDecl* vi_iface_decl =
      item->data_type.kind == DataTypeKind::kVirtualInterface
          ? FindModule(item->data_type.type_name)
          : nullptr;
  RegisterVirtualInterfaceVarDecl(
      item, vi_iface_decl,
      {vi_var_interface_types_, vi_var_modports_, vi_var_param_values_}, diag_);

  RtlirVariable var;
  var.name = ScopedName(item->name);
  // A packed dimension may reference a parameter (e.g. `logic [W-1:0]`), so the
  // width must be evaluated in the module's parameter scope (10.3.3 / A.2.2.1).
  var.width = EvalTypeWidth(item->data_type, typedefs_, BuildParamScope(mod));
  ValidatePackedDimRange(item->data_type, item->loc);
  SetVariableKindFlags(item, var, typedefs_);
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

  SetVariableTypeInfo(item, var);

  ComputeUnpackedDims(item->unpacked_dims, var, {typedefs_, class_names_},
                      diag_, item->loc);
  ValidateUnpackedDimRange(item->unpacked_dims, item->loc);
  InferDynArraySize(item->unpacked_dims, item->init_expr, var);

  TrackVarArrayInfo(item, var);

  var.attrs = ResolveAttributes(item->attrs, diag_, BuildParamScope(mod));
  mod->variables.push_back(var);
  ValidateArrayInitPattern(item);
  ValidateStructInitPattern(item);

  ValidateVarDeclTypes(item, BuildParamScope(mod));
  TrackEnumVariable(item);
}

}  // namespace delta
