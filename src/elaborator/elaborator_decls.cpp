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
#include "elaborator/elaborator_decls_internal.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

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
  if (dim->kind != ExprKind::kIdentifier || dim->text != "$") return false;
  var.is_queue = true;
  if (dim->rhs) {
    // §7.10: the optional right bound is a constant_expression that shall
    // evaluate to a positive integer. Per §11.2.1 that expression may name a
    // parameter or localparam, so it is evaluated in the enclosing parameter
    // scope — just like a range dimension's bounds.
    auto max_val = ConstEvalInt(dim->rhs, scope);
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

static bool TryParseRangeDim(const Expr* dim, RtlirVariable& var,
                             const ScopeMap& scope) {
  if (dim->kind != ExprKind::kBinary || dim->op != TokenKind::kColon)
    return false;
  // §7.4.2: each bound is a constant_expression, which per §11.2.1 may name a
  // parameter or localparam. Evaluate in the module's parameter scope so a
  // dimension such as `[N-1:0]` resolves just as a packed dimension does.
  auto lval = ConstEvalInt(dim->lhs, scope);
  auto rval = ConstEvalInt(dim->rhs, scope);
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
    // An index type is a data_type (§7.8), so it may carry the signing that
    // A.2.2.1 allows on an integer type. That overrides the default: keys of
    // a `byte unsigned` index order 0 to 255, not -128 to 127.
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
                                       DiagEngine& diag, SourceLoc loc,
                                       const ScopeMap& scope) {
  // §7.4.2 / §11.2.1: the single-number `[size]` form is a constant integer
  // expression and may be a parameter or localparam, so it is evaluated in the
  // module's parameter scope.
  auto size_val = ConstEvalInt(dim, scope);
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

void ComputeUnpackedDims(const std::vector<Expr*>& dims, RtlirVariable& var,
                         const UnpackedDimContext& ctx) {
  if (dims.empty() || !dims[0]) return;
  auto* dim = dims[0];
  if (TryParseQueueDim(dim, var, ctx.diag, ctx.loc, ctx.scope)) return;
  if (TryParseAssocDim(dim, var)) return;
  if (TryParseUserDefinedAssocDim(dim, var, ctx.types.typedefs,
                                  ctx.types.class_names))
    return;
  if (TryParseRangeDim(dim, var, ctx.scope)) return;

  ApplyConstSizedUnpackedDim(dim, var, ctx.diag, ctx.loc, ctx.scope);
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
void CheckDeclRedeclaration(const ModuleItem* item,
                            const DeclTypeRef& decl_type, DeclNameTables tables,
                            std::string_view kind_word, DiagEngine& diag) {
  CheckPortNameRedeclaration(item, tables, diag);
  CheckPartialPortOrNameRedeclaration(item, decl_type, tables, kind_word, diag);
}

// §6.7.1 item a / §6.11.1: a packed structure or union is an integral type,
// but per §7.2.1 it is treated as a 2-state vector when every one of its
// members is 2-state. Report such an aggregate as conclusively 2-state. A
// member of any other kind (a 4-state integer, an enum, or a named/nested
// aggregate that could resolve to a 4-state type) leaves the result 4-state,
// so the aggregate is not rejected.
static bool PackedAggregateIsAll2State(const DataType& dtype) {
  if (dtype.struct_members.empty()) return false;
  for (const auto& m : dtype.struct_members) {
    switch (m.type_kind) {
      case DataTypeKind::kBit:
      case DataTypeKind::kByte:
      case DataTypeKind::kShortint:
      case DataTypeKind::kInt:
      case DataTypeKind::kLongint:
        break;
      default:
        return false;
    }
  }
  return true;
}

// §6.7.1 item b: a member of one of these types can never itself be a net
// (they are neither integral nor an aggregate of nets), so an unpacked
// struct/union containing such a member is not a valid net data type.
static bool MemberKindCannotBeNet(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kReal:
    case DataTypeKind::kShortreal:
    case DataTypeKind::kRealtime:
    case DataTypeKind::kString:
    case DataTypeKind::kChandle:
    case DataTypeKind::kEvent:
    case DataTypeKind::kVoid:
      return true;
    default:
      return false;
  }
}

// §6.7.1 / §23.2.2.1: a net declared with a vector type that cannot carry a
// 4-state value is rejected. Item a of §6.7.1 requires a 4-state integral type
// (see §6.11.1); a plain 2-state integer net type, or a packed struct/union
// whose members are all 2-state, is not legal. Item b allows a fixed-size
// unpacked struct/union, but only when each member is itself a valid net type.
// §6.7.1 item b: a struct/union net data type. A packed (or soft-packed)
// aggregate is a net data type only if it is not all-2-state. An unpacked one's
// members must each be a valid net type: a directly non-net member kind (real,
// string, chandle, ...) makes the whole aggregate invalid.
static void ValidateAggregateNetDataType(const DataType& dtype,
                                         DiagEngine& diag, SourceLoc loc) {
  if (dtype.is_packed || dtype.is_soft) {
    if (PackedAggregateIsAll2State(dtype))
      diag.Error(loc, "net data type must be 4-state");
    return;
  }
  for (const auto& m : dtype.struct_members) {
    if (MemberKindCannotBeNet(m.type_kind)) {
      diag.Error(loc,
                 "unpacked struct/union net member must be a valid net "
                 "data type");
      return;
    }
  }
}

static void ValidateNetDataTypeIs4State(const DataType& dtype, DiagEngine& diag,
                                        SourceLoc loc) {
  if (dtype.is_interconnect) return;
  DataTypeKind k = dtype.kind;
  if (k == DataTypeKind::kStruct || k == DataTypeKind::kUnion) {
    ValidateAggregateNetDataType(dtype, diag, loc);
    return;
  }
  if (k != DataTypeKind::kEnum && k != DataTypeKind::kNamed &&
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
                                   const CompilationUnit* unit,
                                   const ScopeMap& scope) {
  if (net.net_type == NetType::kTrireg &&
      item->data_type.charge_strength == 0 &&
      unit->has_default_trireg_strength) {
    net.trireg_capacitance = unit->default_trireg_strength;
  }
  if (item->net_delay_decay) {
    // §28.16.2: the third delay specifies the charge decay time, which is a
    // constant expression -- evaluate it in the module's parameter scope so a
    // parameter or localparam decay time resolves, not just a bare literal.
    net.decay_ticks = static_cast<uint64_t>(
        ConstEvalInt(item->net_delay_decay, scope).value_or(0));
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
  // §6.20.2: a parameter is a constant, so it is legal in the packed dimension
  // of a declaration and has to be folded for the range to have a size. The
  // module's parameter scope is what carries the values, and without it a range
  // naming one does not fold and the net falls back to a single bit. This is
  // the same scope the variable declaration beside it folds against.
  net.width = EvalTypeWidth(item->data_type, typedefs_, BuildParamScope(mod));
  net.is_signed = IsSignedType(item->data_type, typedefs_);
  if (non_ansi_partial_ports_.count(item->name)) {
    net.is_signed =
        ReconcilePartialPortSignedness(item->name, net.is_signed, mod);
  }
  ValidatePackedDimRange(item->data_type, item->loc);

  ValidateNetDataTypeIs4State(item->data_type, diag_, item->loc);

  // §6.7.1: an interconnect net shall specify at most one delay value. A single
  // delay (net_delay) is permitted; a second or third delay term is not.
  if (item->data_type.is_interconnect &&
      (item->net_delay_fall != nullptr || item->net_delay_decay != nullptr)) {
    diag_.Error(item->loc,
                "interconnect net shall specify at most one delay value");
  }

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

  ApplyTriregNetDefaults(item, net, unit_, BuildParamScope(mod));

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
// for any packed declaration — the type itself, since a width alone does not
// say which bit an index addresses. §7.4.1: a packed multidimensional array
// (e.g. `logic [1:0][7:0]`) needs the inner dimensions so the lowerer can
// compute the outermost-element stride and a single-index select slices a whole
// element rather than one bit. §11.5.1: a single packed dimension is equally
// needed, because "the actual bit that is accessed by an address is, in part,
// determined by the declaration" — `logic [15:0] acc` and `logic [2:17] acc`
// are both sixteen bits wide and the same index names a different bit of each,
// so the bounds as written have to reach the lowerer.
void Elaborator::SetVariableTypeInfo(const ModuleItem* item,
                                     RtlirVariable& var) {
  SetStructTypeInfo(item, var, typedefs_, arena_);
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    var.class_type_name = item->data_type.type_name;
  }
  SetEnumTypeInfo(item, var, typedefs_, arena_);
  if (!var.dtype && (item->data_type.packed_dim_left != nullptr ||
                     !item->data_type.extra_packed_dims.empty())) {
    var.dtype = &item->data_type;
  }
}

}  // namespace delta
