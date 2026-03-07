#include "elaborator/elaborator.h"

#include <algorithm>
#include <cstdlib>
#include <format>
#include <optional>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// Defined in elaborator_gates.cpp.
void ElaborateGateInst(ModuleItem* item, RtlirModule* mod, Arena& arena);

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

// §5.12: Evaluate a single AST attribute into a ResolvedAttribute.
static ResolvedAttribute EvalAttribute(const Attribute& attr) {
  ResolvedAttribute ra;
  ra.name = attr.name;
  if (!attr.value) {
    ra.resolved_value = 1;
    return ra;
  }
  if (attr.value->kind == ExprKind::kStringLiteral) {
    auto txt = attr.value->text;
    if (txt.size() >= 2 && txt.front() == '"' && txt.back() == '"') {
      ra.string_value = txt.substr(1, txt.size() - 2);
    } else {
      ra.string_value = txt;
    }
  } else {
    ra.resolved_value = ConstEvalInt(attr.value);
  }
  return ra;
}

// §5.12: Resolve AST attributes into RTLIR ResolvedAttributes.
// Deduplicates (last wins) and evaluates constant expressions.
static std::vector<ResolvedAttribute> ResolveAttributes(
    const std::vector<Attribute>& attrs, DiagEngine& diag) {
  std::vector<ResolvedAttribute> result;
  for (const auto& attr : attrs) {
    auto ra = EvalAttribute(attr);
    auto it = std::find_if(result.begin(), result.end(),
                           [&](const auto& e) { return e.name == ra.name; });
    if (it != result.end()) {
      diag.Warning(
          attr.loc,
          std::format("duplicate attribute '{}'; last value used", attr.name));
      *it = ra;
    } else {
      result.push_back(ra);
    }
  }
  return result;
}

Elaborator::Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit)
    : arena_(arena), diag_(diag), unit_(unit) {}

void Elaborator::ValidateNameSpaces() {
  // §3.13(a): Definitions name space — module, primitive, program, interface
  // names must be unique across all design elements.
  std::unordered_map<std::string_view, SourceRange> def_names;
  auto check_def = [&](std::string_view name, SourceRange range) {
    auto [it, inserted] = def_names.try_emplace(name, range);
    if (!inserted) {
      diag_.Error(range.start,
                  std::format("duplicate definition of '{}'", name));
    }
  };
  for (auto* m : unit_->modules) check_def(m->name, m->range);
  for (auto* p : unit_->programs) check_def(p->name, p->range);
  for (auto* i : unit_->interfaces) check_def(i->name, i->range);
  for (auto* c : unit_->checkers) check_def(c->name, c->range);
  for (auto* u : unit_->udps) check_def(u->name, u->range);

  // §3.13(b): Package name space — package names must be unique.
  std::unordered_set<std::string_view> pkg_names;
  for (auto* pkg : unit_->packages) {
    if (!pkg_names.insert(pkg->name).second) {
      diag_.Error(pkg->range.start,
                  std::format("duplicate package '{}'", pkg->name));
    }
  }
}

RtlirDesign* Elaborator::Elaborate(std::string_view top_module_name) {
  // §3.13: Validate definitions and package name spaces.
  ValidateNameSpaces();
  // §3.12.1: Register CU-scope typedefs and classes before module elaboration.
  RegisterCuScopeItems();
  // §8.13: Check that no class extends a :final class.
  ValidateFinalClassExtension();
  // §8.17: Validate chaining constructor rules.
  ValidateChainingConstructors();
  // §8.19: Validate constant class property rules.
  ValidateConstClassProperties();
  // §8.20: Validate virtual method override rules.
  ValidateVirtualMethodOverrides();
  // §8.21: Validate abstract class and pure virtual method rules.
  ValidateAbstractClassRules();

  auto* mod_decl = FindModule(top_module_name);
  if (!mod_decl) {
    diag_.Error({}, std::format("top module '{}' not found", top_module_name));
    return nullptr;
  }

  auto* design = arena_.Create<RtlirDesign>();
  ParamList empty_params;
  auto* top = ElaborateModule(mod_decl, empty_params);
  if (!top) return nullptr;

  ApplyDefparams(top, mod_decl);

  design->top_modules.push_back(top);
  design->all_modules[top->name] = top;
  // §3.12.1: CU-scope functions/tasks available to all modules.
  for (auto* item : unit_->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      design->cu_function_decls.push_back(item);
    }
  }
  // §20.6.2: Populate type widths for $bits(type) support.
  for (const auto& [name, dtype] : typedefs_) {
    design->type_widths[name] = EvalTypeWidth(dtype, typedefs_);
  }
  return design;
}

// §3.12.1: Register CU-scope typedefs, classes, and imports so they are
// visible during module elaboration.
void Elaborator::RegisterCuScopeItems() {
  for (auto* item : unit_->cu_items) {
    if (!item->name.empty()) cu_scope_names_.insert(item->name);
    if (item->kind == ModuleItemKind::kTypedef) {
      typedefs_[item->name] = item->typedef_type;
    } else if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      class_names_.insert(item->class_decl->name);
    }
  }
  for (auto* cls : unit_->classes) {
    class_names_.insert(cls->name);
    cu_scope_names_.insert(cls->name);
  }
}

ModuleItem* Elaborator::FindCuScopeItem(std::string_view name) const {
  for (auto* item : unit_->cu_items) {
    if (item->name == name) return item;
  }
  return nullptr;
}

ModuleDecl* Elaborator::FindModule(std::string_view name) const {
  auto it = std::find_if(unit_->modules.begin(), unit_->modules.end(),
                         [name](auto* mod) { return mod->name == name; });
  if (it != unit_->modules.end()) return *it;

  // §24: Programs can be instantiated like modules.
  auto pit = std::find_if(unit_->programs.begin(), unit_->programs.end(),
                          [name](auto* p) { return p->name == name; });
  if (pit != unit_->programs.end()) return *pit;

  // §25: Interfaces can be instantiated.
  auto iit = std::find_if(unit_->interfaces.begin(), unit_->interfaces.end(),
                          [name](auto* i) { return i->name == name; });
  if (iit != unit_->interfaces.end()) return *iit;

  // §17: Checkers can be instantiated.
  auto cit = std::find_if(unit_->checkers.begin(), unit_->checkers.end(),
                          [name](auto* c) { return c->name == name; });
  if (cit != unit_->checkers.end()) return *cit;

  return nullptr;
}

static std::optional<int64_t> FindParamOverride(
    const Elaborator::ParamList& params, std::string_view name) {
  for (const auto& [oname, oval] : params) {
    if (oname == name) {
      return oval;
    }
  }
  return std::nullopt;
}

RtlirModule* Elaborator::ElaborateModule(const ModuleDecl* decl,
                                         const ParamList& params) {
  auto* mod = arena_.Create<RtlirModule>();
  mod->name = decl->name;
  // §E.4-E.7: propagate delay mode directive.
  mod->delay_mode = unit_->delay_mode_directive;
  // §5.12: Resolve attributes on module definition.
  mod->attrs = ResolveAttributes(decl->attrs, diag_);

  for (const auto& [pname, pval] : decl->params) {
    RtlirParamDecl pd;
    pd.name = pname;
    pd.default_value = pval;
    pd.is_resolved = false;

    auto override_val = FindParamOverride(params, pname);
    if (override_val) {
      pd.resolved_value = *override_val;
      pd.is_resolved = true;
      pd.from_override = true;
    }
    if (!pd.is_resolved && pval) {
      pd.resolved_value = ConstEvalInt(pval).value_or(0);
      pd.is_resolved = ConstEvalInt(pval).has_value();
    }

    mod->params.push_back(pd);
  }

  ElaboratePorts(decl, mod);
  ElaborateItems(decl, mod);
  return mod;
}

// --- Port elaboration ---

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  for (const auto& port : decl->ports) {
    // §6.14: chandle cannot be used as a port type.
    if (port.data_type.kind == DataTypeKind::kChandle) {
      diag_.Error(port.loc, "chandle cannot be used as a port type");
      continue;
    }
    RtlirPort rp;
    rp.name = port.name;
    rp.direction = port.direction;
    rp.type_kind = port.data_type.kind;
    rp.width = EvalTypeWidth(port.data_type, typedefs_);
    rp.is_signed = port.data_type.is_signed;
    mod->ports.push_back(rp);
  }
}

// --- Module item elaboration ---

uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod) {
  if (!lhs || lhs->kind != ExprKind::kIdentifier) return 0;
  for (const auto& v : mod->variables) {
    if (v.name == lhs->text) return v.width;
  }
  for (const auto& n : mod->nets) {
    if (n.name == lhs->text) return n.width;
  }
  for (const auto& p : mod->ports) {
    if (p.name == lhs->text) return p.width;
  }
  return 0;
}

static RtlirProcessKind MapAlwaysKind(AlwaysKind ak) {
  switch (ak) {
    case AlwaysKind::kAlways:
      return RtlirProcessKind::kAlways;
    case AlwaysKind::kAlwaysComb:
      return RtlirProcessKind::kAlwaysComb;
    case AlwaysKind::kAlwaysFF:
      return RtlirProcessKind::kAlwaysFF;
    case AlwaysKind::kAlwaysLatch:
      return RtlirProcessKind::kAlwaysLatch;
  }
  return RtlirProcessKind::kAlwaysComb;
}

static void AddProcess(RtlirProcessKind kind, ModuleItem* item,
                       RtlirModule* mod, Arena& arena, DiagEngine& diag) {
  RtlirProcess proc;
  proc.kind = kind;
  proc.body = item->body;
  proc.sensitivity = item->sensitivity;
  bool needs_infer = (kind == RtlirProcessKind::kAlwaysComb ||
                      kind == RtlirProcessKind::kAlwaysLatch);
  if (needs_infer && proc.sensitivity.empty()) {
    proc.sensitivity = InferSensitivity(proc.body, arena);
  }
  // §5.12: Resolve attributes.
  proc.attrs = ResolveAttributes(item->attrs, diag);
  mod->processes.push_back(proc);
}

// §7.5: Check for dynamic array [] with init to infer size from elements.
static void InferDynArraySize(const std::vector<Expr*>& dims, const Expr* init,
                              RtlirVariable& var) {
  if (dims.empty() || dims[0] != nullptr) return;  // Not a dynamic array.
  if (var.is_queue || var.is_assoc) return;        // Already classified.
  var.is_dynamic = true;
  if (init && !init->elements.empty()) {
    var.unpacked_size = static_cast<uint32_t>(init->elements.size());
  }
}

// §7.4: Extract unpacked array size from dimension expressions.
// §7.10: Detect queue [$] or [$:N].
static bool TryParseQueueDim(const Expr* dim, RtlirVariable& var) {
  if (dim->kind != ExprKind::kIdentifier || dim->text != "$") return false;
  var.is_queue = true;
  if (dim->rhs) {
    auto max_val = ConstEvalInt(dim->rhs);
    if (max_val) var.queue_max_size = static_cast<int32_t>(*max_val + 1);
  }
  return true;
}

// §7.4: Parse range dimension [hi:lo] or [lo:hi].
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

// §7.8: Detect associative array index type [string], [int], [*], etc.
// §7.9.8: Map index type name to its bit-width for traversal validation.
static uint32_t AssocIndexWidth(std::string_view t) {
  if (t == "byte") return 8;
  if (t == "shortint") return 16;
  if (t == "longint") return 64;
  return 32;  // int, integer, *, default
}

static bool TryParseAssocDim(const Expr* dim, RtlirVariable& var) {
  if (dim->kind != ExprKind::kIdentifier) return false;
  auto t = dim->text;
  if (t == "string" || t == "int" || t == "integer" || t == "byte" ||
      t == "shortint" || t == "longint" || t == "*") {
    var.is_assoc = true;
    var.is_string_index = (t == "string");
    var.assoc_index_width = AssocIndexWidth(t);
    return true;
  }
  return false;
}

// §7.8.5: Check if an identifier is a user-defined type for assoc index.
static bool IsUserDefinedType(
    std::string_view name, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  return typedefs.count(name) > 0 || class_names.count(name) > 0;
}

static void ComputeUnpackedDims(
    const std::vector<Expr*>& dims, RtlirVariable& var,
    const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  if (dims.empty() || !dims[0]) return;
  auto* dim = dims[0];
  if (TryParseQueueDim(dim, var)) return;
  if (TryParseAssocDim(dim, var)) return;
  // §7.8.5: User-defined type (struct, class, enum) as assoc array index.
  if (dim->kind == ExprKind::kIdentifier &&
      IsUserDefinedType(dim->text, typedefs, class_names)) {
    var.is_assoc = true;
    return;
  }
  if (TryParseRangeDim(dim, var)) return;
  // Simple size [N] — creates N elements indexed from 0.
  auto size_val = ConstEvalInt(dim);
  if (size_val && *size_val > 0) {
    var.unpacked_size = static_cast<uint32_t>(*size_val);
  }
}

void Elaborator::ElaborateNetDecl(ModuleItem* item, RtlirModule* mod) {
  if (!declared_names_.insert(item->name).second) {
    diag_.Error(item->loc, std::format("redeclaration of '{}'", item->name));
  }
  var_types_[item->name] = item->data_type.kind;
  RtlirNet net;
  net.name = ScopedName(item->name);
  // §6.6.8: interconnect nets are typeless generic nets.
  if (item->data_type.is_interconnect) {
    net.net_type = NetType::kInterconnect;
    interconnect_names_.insert(item->name);
  } else {
    net.net_type = DataTypeToNetType(item->data_type.kind);
  }
  net.width = EvalTypeWidth(item->data_type, typedefs_);
  // §6.6.4: Extract charge strength and decay time for trireg nets.
  if (item->data_type.charge_strength != 0) {
    net.charge_strength =
        static_cast<Strength>(item->data_type.charge_strength);
  }
  // §E.3: apply `default_trireg_strength to trireg nets without explicit
  // strength.
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
    // §E.2: apply `default_decay_time to trireg nets without explicit decay.
    net.decay_ticks = unit_->default_decay_time;
  }
  // §5.12: Resolve attributes.
  net.attrs = ResolveAttributes(item->attrs, diag_);
  mod->nets.push_back(net);
}

// §6.23: Resolve type(expr) to concrete type kind from declared variables.
// §6.19/§6.24.2: Set enum type name on variable for $cast validation.
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
    // Arena-allocate copy: typedefs_ map is destroyed with the Elaborator,
    // but var.dtype must survive until after lowering.
    var.dtype = arena.Create<DataType>(it->second);
  }
}

// §7.2: Resolve struct/union type info for field-level access.
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
  // Arena-allocate copy: typedefs_ map is destroyed with the Elaborator,
  // but var.dtype must survive until after lowering.
  var.dtype = arena_.Create<DataType>(td->second);
}

void Elaborator::ElaborateVarDecl(ModuleItem* item, RtlirModule* mod) {
  ResolveTypeRef(item, mod);
  // §6.25: Resolve parameterized class scope types (cls#(T)::member).
  ResolveParameterizedType(item->data_type);
  // §6.6.7: If the type is a user-defined nettype, create a net.
  if (item->data_type.kind == DataTypeKind::kNamed &&
      nettype_names_.count(item->data_type.type_name)) {
    item->data_type.is_net = true;
    item->kind = ModuleItemKind::kNetDecl;
    ElaborateNetDecl(item, mod);
    return;
  }
  if (!declared_names_.insert(item->name).second) {
    diag_.Error(item->loc, std::format("redeclaration of '{}'", item->name));
  }
  // §6.20.6: Const variables must have an initializer.
  if (item->data_type.is_const) {
    if (!item->init_expr) {
      diag_.Error(
          item->loc,
          std::format("const variable '{}' must be initialized", item->name));
    }
    const_names_.insert(item->name);
  }
  var_types_[item->name] = item->data_type.kind;
  RtlirVariable var;
  var.name = ScopedName(item->name);
  var.width = EvalTypeWidth(item->data_type, typedefs_);
  var.is_4state = Is4stateType(item->data_type, typedefs_);
  var.is_event = (item->data_type.kind == DataTypeKind::kEvent);
  var.is_string = (item->data_type.kind == DataTypeKind::kString);
  var.is_real = (item->data_type.kind == DataTypeKind::kReal ||
                 item->data_type.kind == DataTypeKind::kShortreal ||
                 item->data_type.kind == DataTypeKind::kRealtime);
  var.is_signed =
      item->data_type.is_signed || IsImplicitlySigned(item->data_type.kind);
  var.init_expr = item->init_expr;
  // Pass struct/union type info for field-level access.
  SetStructTypeInfo(item, var);
  // §8: Mark class-typed variables.
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    var.class_type_name = item->data_type.type_name;
  }
  // §6.19/§6.24.2: Track enum type for $cast validation.
  SetEnumTypeInfo(item, var, typedefs_, arena_);
  // §7.4/§7.5: Compute unpacked array element count.
  ComputeUnpackedDims(item->unpacked_dims, var, typedefs_, class_names_);
  InferDynArraySize(item->unpacked_dims, item->init_expr, var);
  // §7.6/§7.9.9: Track array info for assignment compatibility.
  if (!item->unpacked_dims.empty()) {
    VarArrayInfo info{item->data_type.kind, var.unpacked_size, var.is_dynamic,
                      var.is_assoc, {}};
    if (var.is_assoc && !item->unpacked_dims.empty() &&
        item->unpacked_dims[0] &&
        item->unpacked_dims[0]->kind == ExprKind::kIdentifier) {
      info.assoc_index_type = item->unpacked_dims[0]->text;
    }
    var_array_info_[item->name] = info;
  }
  // §5.12: Resolve attributes.
  var.attrs = ResolveAttributes(item->attrs, diag_);
  mod->variables.push_back(var);
  ValidateArrayInitPattern(item);
  ValidateStructInitPattern(item);
  TrackEnumVariable(item);
  // §8.4: Track class-typed variables for operator restriction checks.
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    class_var_names_.insert(item->name);
    class_var_types_[item->name] = item->data_type.type_name;
  }
  if (item->data_type.kind == DataTypeKind::kEnum) {
    ValidateEnumDecl(item->data_type, item->loc);
  }
  if (item->data_type.kind == DataTypeKind::kStruct ||
      item->data_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->data_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->data_type, item->loc);
    ValidateVoidMembers(item->data_type, item->loc);
    ValidateRandQualifiers(item->data_type, item->loc);
    ValidatePackedStructMemberTypes(item->data_type, item->loc);
    ValidateChandleInUnion(item->data_type, item->loc);
    ValidatePackedUnion(item->data_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->data_type, item->loc);
  ValidateAssocIndexType(item);
}

// §6.20.5: Elaborate a specparam as a simulation-accessible constant variable.
void Elaborator::ElaborateSpecparam(ModuleItem* item, RtlirModule* mod) {
  RtlirVariable var;
  var.name = ScopedName(item->name);
  var.width = 32;
  var.init_expr = item->init_expr;
  mod->variables.push_back(var);
}

// §6.10: Check if an identifier is already declared as a variable, net, or
// port.
static bool IsNameDeclared(std::string_view name, const RtlirModule* mod) {
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
  RtlirNet net;
  net.name = ScopedName(name);
  net.net_type = unit_->default_nettype;
  net.width = 1;  // §6.10: Implicit nets are scalar.
  mod->nets.push_back(net);
  declared_names_.insert(name);
  return true;
}

void Elaborator::ElaborateContAssign(ModuleItem* item, RtlirModule* mod) {
  if (item->assign_lhs && item->assign_lhs->kind == ExprKind::kIdentifier) {
    auto name = item->assign_lhs->text;
    MaybeCreateImplicitNet(name, item->loc, mod);
    if (!cont_assign_targets_.emplace(name, item->loc).second) {
      diag_.Error(item->loc,
                  std::format("multiple continuous assignments to '{}'", name));
    }
  }
  RtlirContAssign ca;
  ca.lhs = item->assign_lhs;
  ca.rhs = item->assign_rhs;
  ca.width = LookupLhsWidth(ca.lhs, mod);
  ca.drive_strength0 = item->drive_strength0;
  ca.drive_strength1 = item->drive_strength1;
  ca.delay = item->assign_delay;
  ca.delay_fall = item->assign_delay_fall;
  ca.delay_decay = item->assign_delay_decay;
  // §5.12: Resolve attributes.
  ca.attrs = ResolveAttributes(item->attrs, diag_);
  mod->assigns.push_back(ca);
}

void Elaborator::ElaborateParamDecl(ModuleItem* item, RtlirModule* mod) {
  // §6.20.3: Type parameters register as typedefs.
  if (item->data_type.kind == DataTypeKind::kVoid &&
      item->typedef_type.kind != DataTypeKind::kImplicit) {
    typedefs_[item->name] = item->typedef_type;
  }
  RtlirParamDecl pd;
  pd.name = item->name;
  pd.default_value = item->init_expr;
  // §6.20.7: detect $ as unbounded parameter value.
  if (item->init_expr && item->init_expr->kind == ExprKind::kIdentifier &&
      item->init_expr->text == "$") {
    pd.is_unbounded = true;
  } else if (item->init_expr) {
    auto scope = BuildParamScope(mod);
    auto val = ConstEvalInt(item->init_expr, scope);
    if (val) {
      pd.resolved_value = *val;
      pd.is_resolved = true;
    }
  }
  mod->params.push_back(pd);
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
      AddProcess(MapAlwaysKind(item->always_kind), item, mod, arena_, diag_);
      break;
    case ModuleItemKind::kModuleInst:
      ElaborateModuleInst(item, mod);
      break;
    case ModuleItemKind::kParamDecl:
      ElaborateParamDecl(item, mod);
      break;
    case ModuleItemKind::kGenerateIf:
      ElaborateGenerateIf(item, mod, BuildParamScope(mod));
      break;
    case ModuleItemKind::kGenerateCase:
      ElaborateGenerateCase(item, mod, BuildParamScope(mod));
      break;
    case ModuleItemKind::kGenerateFor:
      ElaborateGenerateFor(item, mod, BuildParamScope(mod));
      break;
    case ModuleItemKind::kTypedef:
      ElaborateTypedef(item, mod);
      break;
    case ModuleItemKind::kNettypeDecl:
      ElaborateNettypeDecl(item, mod);
      break;
    case ModuleItemKind::kFunctionDecl:
      ValidateFunctionBody(item);
      mod->function_decls.push_back(item);
      break;
    case ModuleItemKind::kTaskDecl:
      mod->function_decls.push_back(item);
      break;
    case ModuleItemKind::kGateInst:
      ElaborateGateInst(item, mod, arena_);
      break;
    case ModuleItemKind::kUdpInst:
      break;
    case ModuleItemKind::kSpecparam:
      specparam_names_.insert(item->name);
      ElaborateSpecparam(item, mod);
      break;
    case ModuleItemKind::kAlias: {
      RtlirAlias alias;
      alias.nets = item->alias_nets;
      mod->aliases.push_back(alias);
      break;
    }
    case ModuleItemKind::kDefparam:
    case ModuleItemKind::kImportDecl:
    case ModuleItemKind::kExportDecl:
    case ModuleItemKind::kPropertyDecl:
    case ModuleItemKind::kSequenceDecl:
    case ModuleItemKind::kAssertProperty:
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kCoverSequence:
    case ModuleItemKind::kRestrictProperty:
    case ModuleItemKind::kClockingBlock:
    case ModuleItemKind::kCovergroupDecl:
    case ModuleItemKind::kSpecifyBlock:
    case ModuleItemKind::kDpiImport:
    case ModuleItemKind::kDpiExport:
    case ModuleItemKind::kLetDecl:
    case ModuleItemKind::kElabSystemTask:
    case ModuleItemKind::kDefaultDisableIff:
    case ModuleItemKind::kNestedModuleDecl:
    case ModuleItemKind::kClassDecl:
      if (item->class_decl) {
        class_names_.insert(item->class_decl->name);
        mod->class_decls.push_back(item->class_decl);
      }
      break;
  }
}

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  typedefs_[item->name] = item->typedef_type;
  if (item->typedef_type.kind == DataTypeKind::kStruct ||
      item->typedef_type.kind == DataTypeKind::kUnion) {
    ValidatePackedStructDefaults(item->typedef_type, item->loc);
    ValidateUnpackedStructWithUnionDefaults(item->typedef_type, item->loc);
    ValidateVoidMembers(item->typedef_type, item->loc);
    ValidateRandQualifiers(item->typedef_type, item->loc);
    ValidatePackedStructMemberTypes(item->typedef_type, item->loc);
    ValidateChandleInUnion(item->typedef_type, item->loc);
    ValidatePackedUnion(item->typedef_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->typedef_type, item->loc);
  if (item->typedef_type.kind != DataTypeKind::kEnum) return;
  ValidateEnumDecl(item->typedef_type, item->loc);
  int64_t next_val = 0;
  std::vector<RtlirEnumMember> members;
  for (const auto& member : item->typedef_type.enum_members) {
    enum_member_names_.insert(member.name);
    if (member.value) {
      next_val = ConstEvalInt(member.value).value_or(next_val);
    }
    members.push_back({member.name, next_val});
    RtlirVariable var;
    var.name = member.name;
    var.width = EvalTypeWidth(item->typedef_type, typedefs_);
    var.is_4state = false;
    mod->variables.push_back(var);
    ++next_val;
  }
  mod->enum_types[item->name] = std::move(members);
}

// §6.6.7: Register a user-defined nettype so declarations using it create nets.
void Elaborator::ElaborateNettypeDecl(ModuleItem* item, RtlirModule* /*mod*/) {
  typedefs_[item->name] = item->typedef_type;
  nettype_names_.insert(item->name);
}

void Elaborator::ElaborateItems(const ModuleDecl* decl, RtlirModule* mod) {
  declared_names_.clear();
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
  interconnect_names_.clear();
  for (auto* item : decl->items) {
    ElaborateItem(item, mod);
  }
  ValidateModuleConstraints(decl);
}

// --- Module instantiation ---

void Elaborator::ElaborateModuleInst(ModuleItem* item, RtlirModule* mod) {
  RtlirModuleInst inst;
  inst.module_name = item->inst_module;
  inst.inst_name = item->inst_name;

  auto* child_decl = FindModule(item->inst_module);
  if (!child_decl) {
    diag_.Warning(item->loc,
                  std::format("unknown module '{}'", item->inst_module));
    mod->children.push_back(inst);
    return;
  }

  ParamList child_params;
  inst.resolved = ElaborateModule(child_decl, child_params);
  BindPorts(inst, item, mod);
  // §5.12: Resolve attributes.
  inst.attrs = ResolveAttributes(item->attrs, diag_);
  mod->children.push_back(inst);
}

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item,
                           RtlirModule* parent_mod) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& [port_name, conn_expr] : item->inst_ports) {
    // §6.10: Create implicit nets for undeclared identifiers in connections.
    if (conn_expr && conn_expr->kind == ExprKind::kIdentifier) {
      MaybeCreateImplicitNet(conn_expr->text, item->loc, parent_mod);
    }
    RtlirPortBinding binding;
    binding.port_name = port_name;
    binding.connection = conn_expr;

    auto it =
        std::find_if(child_ports.begin(), child_ports.end(),
                     [&](const RtlirPort& p) { return p.name == port_name; });
    if (it == child_ports.end()) {
      diag_.Warning(item->loc, std::format("port '{}' not found on module '{}'",
                                           port_name, inst.module_name));
      binding.direction = Direction::kInput;
      binding.width = 1;
    } else {
      binding.direction = it->direction;
      binding.width = it->width;
    }
    inst.port_bindings.push_back(binding);
  }
}

// --- Generate expansion ---

ScopeMap Elaborator::BuildParamScope(const RtlirModule* mod) {
  ScopeMap scope;
  for (const auto& p : mod->params) {
    if (p.is_resolved) {
      scope[p.name] = p.resolved_value;
    }
  }
  return scope;
}

void Elaborator::ElaborateGenerateItems(const std::vector<ModuleItem*>& items,
                                        RtlirModule* mod,
                                        const ScopeMap& scope) {
  for (auto* item : items) {
    switch (item->kind) {
      case ModuleItemKind::kGenerateIf:
        ElaborateGenerateIf(item, mod, scope);
        break;
      case ModuleItemKind::kGenerateCase:
        ElaborateGenerateCase(item, mod, scope);
        break;
      case ModuleItemKind::kGenerateFor:
        ElaborateGenerateFor(item, mod, scope);
        break;
      default:
        ElaborateItem(item, mod);
        break;
    }
  }
}

void Elaborator::ElaborateGenerateIf(ModuleItem* item, RtlirModule* mod,
                                     const ScopeMap& scope) {
  auto cond = ConstEvalInt(item->gen_cond, scope);
  if (!cond) {
    diag_.Warning(item->loc, "generate-if condition is not constant");
    return;
  }
  if (*cond) {
    ElaborateGenerateItems(item->gen_body, mod, scope);
  } else if (item->gen_else) {
    ElaborateGenerateItems(item->gen_else->gen_body, mod, scope);
  }
}

static bool MatchesCasePattern(const std::vector<Expr*>& patterns,
                               int64_t selector, const ScopeMap& scope) {
  for (const auto* pat : patterns) {
    auto val = ConstEvalInt(pat, scope);
    if (val && *val == selector) return true;
  }
  return false;
}

void Elaborator::ElaborateGenerateCase(ModuleItem* item, RtlirModule* mod,
                                       const ScopeMap& scope) {
  auto selector = ConstEvalInt(item->gen_cond, scope);
  if (!selector) {
    diag_.Warning(item->loc, "generate-case selector is not constant");
    return;
  }
  const std::vector<ModuleItem*>* default_body = nullptr;
  for (const auto& ci : item->gen_case_items) {
    if (ci.is_default) {
      default_body = &ci.body;
      continue;
    }
    if (MatchesCasePattern(ci.patterns, *selector, scope)) {
      ElaborateGenerateItems(ci.body, mod, scope);
      return;
    }
  }
  if (default_body) {
    ElaborateGenerateItems(*default_body, mod, scope);
  }
}

std::string_view Elaborator::ScopedName(std::string_view base) {
  if (gen_prefix_.empty()) return base;
  std::string full = gen_prefix_ + std::string(base);
  return {arena_.AllocString(full.c_str(), full.size()), full.size()};
}

static constexpr int64_t kMaxGenerateIterations = 65536;

void Elaborator::ElaborateGenerateFor(ModuleItem* item, RtlirModule* mod,
                                      const ScopeMap& scope) {
  if (!item->gen_init || !item->gen_init->lhs) {
    diag_.Warning(item->loc, "malformed generate-for initializer");
    return;
  }
  auto genvar_name = item->gen_init->lhs->text;
  auto init_val = ConstEvalInt(item->gen_init->rhs, scope);
  if (!init_val) {
    diag_.Warning(item->loc, "generate-for init is not constant");
    return;
  }

  ScopeMap loop_scope = scope;
  loop_scope[genvar_name] = *init_val;
  std::string saved_prefix = gen_prefix_;

  for (int64_t iter = 0; iter < kMaxGenerateIterations; ++iter) {
    auto cond = ConstEvalInt(item->gen_cond, loop_scope);
    if (!cond || !*cond) break;

    gen_prefix_ = std::format("{}{}_{}_", saved_prefix, genvar_name,
                              loop_scope[genvar_name]);
    ElaborateGenerateItems(item->gen_body, mod, loop_scope);

    auto next = ConstEvalInt(item->gen_step->rhs, loop_scope);
    if (!next) break;
    loop_scope[genvar_name] = *next;
  }

  gen_prefix_ = saved_prefix;
}

}  // namespace delta
