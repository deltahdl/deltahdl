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
std::vector<ResolvedAttribute> ResolveAttributes(
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

// §3.1: Recursively collect all elaborated modules from the instantiation
// hierarchy into the design's all_modules map.
static void CollectAllModules(
    RtlirModule* mod,
    std::unordered_map<std::string_view, RtlirModule*>& all_modules) {
  if (!mod) return;
  auto [it, inserted] = all_modules.try_emplace(mod->name, mod);
  if (!inserted) return;  // Already visited (diamond instantiation).
  for (auto& child : mod->children) {
    CollectAllModules(child.resolved, all_modules);
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
  // §8.24: Validate out-of-block method declarations.
  ValidateOutOfBlockDeclarations();
  // §8.26: Validate interface class rules.
  ValidateInterfaceClassRules();
  // §8.27: Validate forward class typedefs are resolved.
  ValidateForwardClassTypedefs();

  ResolveExternModules();

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
  // §3.1: Register the full instantiation hierarchy in the design's module map.
  CollectAllModules(top, design->all_modules);
  // §3.12.1: CU-scope functions/tasks available to all modules.
  for (auto* item : unit_->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      design->cu_function_decls.push_back(item);
    } else if (item->kind == ModuleItemKind::kLetDecl) {
      design->cu_let_decls.push_back(item);
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
  // §15.3: semaphore is a built-in class type in the std package.
  class_names_.insert("semaphore");
  // §15.4: mailbox is a built-in class type in the std package.
  class_names_.insert("mailbox");
  // §8.30.1: weak_reference is a built-in parameterized class in the std package.
  class_names_.insert("weak_reference");
  // §9.7: process is a built-in :final class.
  class_names_.insert("process");
  for (auto* item : unit_->cu_items) {
    if (!item->name.empty()) cu_scope_names_.insert(item->name);
    if (item->kind == ModuleItemKind::kTypedef) {
      typedefs_[item->name] = item->typedef_type;
    } else if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
      class_names_.insert(item->class_decl->name);
      if (!item->class_decl->params.empty())
        parameterized_class_names_.insert(item->class_decl->name);
    } else if (item->kind == ModuleItemKind::kParamDecl && item->init_expr) {
      auto val = ConstEvalInt(item->init_expr, cu_param_scope_);
      if (val) {
        cu_param_scope_[item->name] = *val;
      }
    }
  }
  for (auto* cls : unit_->classes) {
    class_names_.insert(cls->name);
    cu_scope_names_.insert(cls->name);
    if (!cls->params.empty()) parameterized_class_names_.insert(cls->name);
  }
}

ModuleItem* Elaborator::FindCuScopeItem(std::string_view name) const {
  for (auto* item : unit_->cu_items) {
    if (item->name == name) return item;
  }
  return nullptr;
}

void Elaborator::ResolveExternModules() {
  for (auto* mod : unit_->modules) {
    if (mod->is_extern) continue;

    ModuleDecl* extern_decl = nullptr;
    for (auto* other : unit_->modules) {
      if (other->is_extern && other->name == mod->name) {
        extern_decl = other;
        break;
      }
    }
    if (!extern_decl) continue;

    if (mod->has_wildcard_ports) {
      mod->ports = extern_decl->ports;
      if (mod->params.empty() && !extern_decl->params.empty()) {
        mod->params = extern_decl->params;
        mod->type_param_names = extern_decl->type_param_names;
        mod->has_param_port_list = extern_decl->has_param_port_list;
      }
      continue;
    }

    if (extern_decl->ports.size() != mod->ports.size()) {
      diag_.Error(mod->range.start,
                  std::format("module '{}' port count ({}) does not match "
                              "extern declaration ({})",
                              mod->name, mod->ports.size(),
                              extern_decl->ports.size()));
      continue;
    }
    for (size_t i = 0; i < mod->ports.size(); ++i) {
      if (!mod->ports[i].name.empty() && !extern_decl->ports[i].name.empty() &&
          mod->ports[i].name != extern_decl->ports[i].name) {
        diag_.Error(mod->range.start,
                    std::format("module '{}' port '{}' at position {} does not "
                                "match extern declaration port '{}'",
                                mod->name, mod->ports[i].name, i,
                                extern_decl->ports[i].name));
        break;
      }
    }
    if (extern_decl->params.size() != mod->params.size()) {
      diag_.Error(
          mod->range.start,
          std::format("module '{}' parameter count ({}) does not match "
                      "extern declaration ({})",
                      mod->name, mod->params.size(),
                      extern_decl->params.size()));
    }
  }
}

ModuleDecl* Elaborator::FindModule(std::string_view name) const {
  ModuleDecl* extern_decl = nullptr;
  for (auto* mod : unit_->modules) {
    if (mod->name == name) {
      if (!mod->is_extern) return mod;
      if (!extern_decl) extern_decl = mod;
    }
  }
  if (extern_decl) return extern_decl;

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

ModuleDecl* Elaborator::FindModuleInScope(std::string_view name) const {
  auto it = nested_module_decls_.find(name);
  if (it != nested_module_decls_.end()) return it->second;
  return FindModule(name);
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
  mod->has_param_port_list = decl->has_param_port_list;
  // §E.4-E.7: propagate delay mode directive.
  mod->delay_mode = unit_->delay_mode_directive;
  // §5.12: Resolve attributes on module definition.
  mod->attrs = ResolveAttributes(decl->attrs, diag_);

  for (const auto& [pname, pval] : decl->params) {
    RtlirParamDecl pd;
    pd.name = pname;
    pd.default_value = pval;
    pd.is_resolved = false;
    pd.is_type_param = decl->type_param_names.count(pname) > 0;
    pd.is_localparam = decl->localparam_port_names.count(pname) > 0;

    auto override_val = FindParamOverride(params, pname);
    if (override_val) {
      pd.resolved_value = *override_val;
      pd.is_resolved = true;
      pd.from_override = true;
    }
    if (!pd.is_resolved && pval) {
      if (pval->kind == ExprKind::kIdentifier && pval->text == "$") {
        pd.is_unbounded = true;
      } else {
        // §6.20.1: Parameters can depend on earlier parameters.
        auto scope = BuildParamScope(mod);
        auto val = ConstEvalInt(pval, scope);
        pd.resolved_value = val.value_or(0);
        pd.is_resolved = val.has_value();
      }
    }

    mod->params.push_back(pd);
  }

  ElaboratePorts(decl, mod);
  ElaborateItems(decl, mod);
  return mod;
}

// --- Port elaboration ---

void Elaborator::ElaboratePorts(const ModuleDecl* decl, RtlirModule* mod) {
  auto param_scope = BuildParamScope(mod);
  // §23.2.2.1 R5: Duplicate explicit port name check for non-ANSI modules.
  if (decl->is_non_ansi_ports) {
    std::unordered_set<std::string_view> explicit_names;
    for (const auto& port : decl->ports) {
      if (port.is_explicit_named && !port.name.empty()) {
        if (!explicit_names.insert(port.name).second) {
          diag_.Error(port.loc,
                      std::format("duplicate port name '.{}'", port.name));
        }
      }
    }
  }

  if (!decl->is_non_ansi_ports) {
    for (const auto& port : decl->ports) {
      if (!port.name.empty()) {
        if (!ansi_port_names_.insert(port.name).second) {
          diag_.Error(port.loc,
                      std::format("duplicate port name '{}'", port.name));
        }
      }
    }
  }

  for (const auto& port : decl->ports) {
    // §6.14: chandle cannot be used as a port type.
    if (port.data_type.kind == DataTypeKind::kChandle) {
      diag_.Error(port.loc, "chandle cannot be used as a port type");
      continue;
    }

    // §23.2.2.1 R9: Non-ANSI implicit ports must have a direction declared
    // in the module body.
    if (decl->is_non_ansi_ports && !port.name.empty() &&
        !port.is_explicit_named && port.direction == Direction::kNone) {
      diag_.Error(port.loc,
                  std::format("port '{}' has no direction declaration in the "
                              "module body",
                              port.name));
    }

    // §23.2.2.1 R11/R12: Track complete vs partial port declarations for
    // body-level net/variable redeclaration validation.
    if (decl->is_non_ansi_ports && !port.name.empty() &&
        port.direction != Direction::kNone) {
      if (port.data_type.kind != DataTypeKind::kImplicit) {
        non_ansi_complete_ports_.insert(port.name);
      } else {
        non_ansi_partial_ports_[port.name] =
            EvalTypeWidth(port.data_type, typedefs_, param_scope);
      }
    }

    if (port.default_value) {
      if (port.direction != Direction::kInput) {
        diag_.Error(port.loc,
                    std::format("default value on {} port '{}'; defaults are "
                                "only allowed on input ports",
                                port.direction == Direction::kOutput  ? "output"
                                : port.direction == Direction::kInout ? "inout"
                                                                     : "ref",
                                port.name));
      }
      if (decl->is_non_ansi_ports) {
        diag_.Error(port.loc,
                    std::format("default value on port '{}'; defaults are "
                                "only allowed with ANSI-style port "
                                "declarations",
                                port.name));
      }
      if (port.data_type.is_interconnect) {
        diag_.Error(port.loc,
                    std::format("default value on interconnect port '{}'",
                                port.name));
      }
      if (!port.unpacked_dims.empty() || !IsSingularType(port.data_type)) {
        diag_.Error(port.loc,
                    std::format("default value on non-singular port '{}'",
                                port.name));
      }
    }

    bool port_is_var =
        !port.data_type.is_net && !port.data_type.is_interconnect;

    if (port.direction == Direction::kInout && port_is_var) {
      diag_.Error(port.loc,
                  std::format("variable data type is not permitted on "
                              "inout port '{}'",
                              port.name));
    }

    RtlirPort rp;
    rp.name = port.name;
    rp.direction = port.direction;
    rp.type_kind = port.data_type.kind;
    rp.width = EvalTypeWidth(port.data_type, typedefs_, param_scope);
    rp.is_signed = port.data_type.is_signed;
    rp.is_var = port_is_var;
    rp.is_interconnect = port.data_type.is_interconnect;
    rp.default_value = port.default_value;

    for (auto* dim : port.unpacked_dims) {
      if (!dim) continue;
      if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
        auto lv = ConstEvalInt(dim->lhs);
        auto rv = ConstEvalInt(dim->rhs);
        if (lv && rv) {
          rp.unpacked_dim_sizes.push_back(
              static_cast<uint32_t>(std::abs(*lv - *rv) + 1));
        }
      } else {
        auto sv = ConstEvalInt(dim);
        if (sv && *sv > 0)
          rp.unpacked_dim_sizes.push_back(static_cast<uint32_t>(*sv));
      }
    }
    rp.num_unpacked_dims =
        static_cast<uint32_t>(rp.unpacked_dim_sizes.size());

    if (port.is_interface_port) {
      rp.is_interface_port = true;
    } else if (port.direction == Direction::kNone &&
               port.data_type.kind == DataTypeKind::kNamed &&
               !port.data_type.type_name.empty()) {
      auto* ifc_decl = FindModule(port.data_type.type_name);
      if (ifc_decl && ifc_decl->decl_kind == ModuleDeclKind::kInterface) {
        rp.is_interface_port = true;
        rp.interface_type_name = port.data_type.type_name;
      }
    }

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

RtlirProcessKind MapAlwaysKind(AlwaysKind ak) {
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

// §9.2.2.2: Check if a statement contains a fork-join construct.
static bool StmtHasForkJoin(const Stmt* stmt) {
  if (!stmt) return false;
  if (stmt->kind == StmtKind::kFork) return true;
  for (const auto* s : stmt->stmts)
    if (StmtHasForkJoin(s)) return true;
  if (StmtHasForkJoin(stmt->then_branch)) return true;
  if (StmtHasForkJoin(stmt->else_branch)) return true;
  if (StmtHasForkJoin(stmt->body)) return true;
  if (StmtHasForkJoin(stmt->for_body)) return true;
  for (const auto& ci : stmt->case_items)
    if (StmtHasForkJoin(ci.body)) return true;
  return false;
}

// §9.2.2.2: Detect incomplete if/case that may infer latched behavior.
static bool MayInferLatch(const Stmt* stmt);

static bool MayInferLatchCase(const Stmt* stmt) {
  bool has_default = false;
  for (const auto& ci : stmt->case_items)
    if (ci.is_default) {
      has_default = true;
      break;
    }
  if (!has_default) return true;
  for (const auto& ci : stmt->case_items)
    if (MayInferLatch(ci.body)) return true;
  return false;
}

static bool MayInferLatch(const Stmt* stmt) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kIf:
      if (!stmt->else_branch) return true;
      return MayInferLatch(stmt->then_branch) ||
             MayInferLatch(stmt->else_branch);
    case StmtKind::kCase:
      return MayInferLatchCase(stmt);
    case StmtKind::kBlock:
      for (const auto* s : stmt->stmts)
        if (MayInferLatch(s)) return true;
      return false;
    default:
      return false;
  }
}

// §9.2.2.1: Check if a statement contains any timing control.
static bool StmtHasTimingControl(const Stmt* stmt) {
  if (!stmt) return false;
  switch (stmt->kind) {
    case StmtKind::kTimingControl:
    case StmtKind::kDelay:
    case StmtKind::kEventControl:
    case StmtKind::kWait:
    case StmtKind::kWaitFork:
      return true;
    case StmtKind::kBlock:
      for (const auto* s : stmt->stmts)
        if (StmtHasTimingControl(s)) return true;
      return false;
    case StmtKind::kIf:
      return StmtHasTimingControl(stmt->then_branch) ||
             StmtHasTimingControl(stmt->else_branch);
    case StmtKind::kFor:
      return StmtHasTimingControl(stmt->for_body);
    case StmtKind::kWhile:
    case StmtKind::kDoWhile:
    case StmtKind::kForever:
    case StmtKind::kRepeat:
    case StmtKind::kForeach:
      return StmtHasTimingControl(stmt->body);
    case StmtKind::kFork:
      for (const auto* s : stmt->fork_stmts)
        if (StmtHasTimingControl(s)) return true;
      return false;
    default:
      return false;
  }
}

static void ValidateCombLatchProcess(ModuleItem* item, const RtlirProcess& proc,
                                     RtlirProcessKind kind, DiagEngine& diag) {
  if (kind != RtlirProcessKind::kAlwaysComb &&
      kind != RtlirProcessKind::kAlwaysLatch)
    return;
  if (StmtHasTimingControl(proc.body)) {
    const char* kw = (kind == RtlirProcessKind::kAlwaysComb) ? "always_comb"
                                                             : "always_latch";
    diag.Error(item->loc,
               std::format("{} shall not contain timing controls", kw));
  }
  if (StmtHasForkJoin(proc.body)) {
    const char* kw = (kind == RtlirProcessKind::kAlwaysComb) ? "always_comb"
                                                             : "always_latch";
    diag.Error(item->loc,
               std::format("{} shall not contain fork-join statements", kw));
  }
  if (kind == RtlirProcessKind::kAlwaysComb && MayInferLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_comb may infer latched behavior; "
                 "ensure all paths assign all outputs");
  }
  if (kind == RtlirProcessKind::kAlwaysLatch && !MayInferLatch(proc.body)) {
    diag.Warning(item->loc,
                 "always_latch does not infer latched behavior; "
                 "ensure incomplete assignments create intended latches");
  }
}

static void ValidateAlwaysFFProcess(ModuleItem* item, const RtlirProcess& proc,
                                    DiagEngine& diag) {
  if (item->sensitivity.empty()) {
    diag.Error(item->loc, "always_ff requires an event control");
  }
  if (StmtHasTimingControl(proc.body)) {
    diag.Error(item->loc,
               "always_ff shall not contain blocking timing controls");
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc, "always_ff shall not contain fork-join statements");
  }
  bool has_edge = false;
  for (const auto& ev : item->sensitivity) {
    if (ev.edge == Edge::kPosedge || ev.edge == Edge::kNegedge) {
      has_edge = true;
      break;
    }
  }
  if (!item->sensitivity.empty() && !has_edge) {
    diag.Warning(item->loc,
                 "always_ff has no edge-sensitive event; "
                 "may not represent sequential logic");
  }
}

static void ValidateFinalProcess(ModuleItem* item, const RtlirProcess& proc,
                                 DiagEngine& diag) {
  if (StmtHasTimingControl(proc.body)) {
    diag.Error(item->loc, "final procedure shall not contain timing controls");
  }
  if (StmtHasForkJoin(proc.body)) {
    diag.Error(item->loc,
               "final procedure shall not contain fork-join statements");
  }
}

void AddProcess(
    RtlirProcessKind kind, ModuleItem* item, RtlirModule* mod, Arena& arena,
    DiagEngine& diag,
    const std::unordered_map<std::string_view, const ModuleItem*>* func_map) {
  RtlirProcess proc;
  proc.kind = kind;
  proc.body = item->body;
  proc.sensitivity = item->sensitivity;
  proc.is_star_sensitivity = item->is_star_sensitivity;
  bool needs_infer = (kind == RtlirProcessKind::kAlwaysComb ||
                      kind == RtlirProcessKind::kAlwaysLatch);
  if (needs_infer && proc.sensitivity.empty()) {
    proc.sensitivity = InferSensitivity(proc.body, arena, func_map);
  }
  if (kind == RtlirProcessKind::kAlways && item->is_star_sensitivity &&
      proc.sensitivity.empty()) {
    proc.sensitivity =
        InferSensitivity(proc.body, arena, nullptr, /*exclude_written=*/false);
  }
  // §9.2.2.1: Warn if a general-purpose always has no timing control.
  if (kind == RtlirProcessKind::kAlways && item->sensitivity.empty() &&
      !item->is_star_sensitivity && !StmtHasTimingControl(proc.body)) {
    diag.Warning(item->loc,
                 "always block has no timing control; may cause "
                 "a zero-delay loop");
  }
  ValidateCombLatchProcess(item, proc, kind, diag);
  if (kind == RtlirProcessKind::kAlwaysFF) {
    ValidateAlwaysFFProcess(item, proc, diag);
  }
  if (kind == RtlirProcessKind::kFinal) {
    ValidateFinalProcess(item, proc, diag);
  }
  // §5.12: Resolve attributes.
  proc.attrs = ResolveAttributes(item->attrs, diag);
  mod->processes.push_back(proc);
}

static void CollectStmtLhsPrefixes(const Stmt* stmt,
                                   std::unordered_set<std::string>& out) {
  if (!stmt) return;
  if (stmt->kind == StmtKind::kBlockingAssign ||
      stmt->kind == StmtKind::kNonblockingAssign) {
    if (stmt->lhs) {
      std::string prefix = LongestStaticPrefix(stmt->lhs);
      if (!prefix.empty()) out.insert(std::move(prefix));
    }
  }
  for (const auto* s : stmt->stmts) CollectStmtLhsPrefixes(s, out);
  CollectStmtLhsPrefixes(stmt->then_branch, out);
  CollectStmtLhsPrefixes(stmt->else_branch, out);
  CollectStmtLhsPrefixes(stmt->body, out);
  CollectStmtLhsPrefixes(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectStmtLhsPrefixes(fi, out);
  for (auto* fs : stmt->for_steps) CollectStmtLhsPrefixes(fs, out);
  for (const auto& ci : stmt->case_items) CollectStmtLhsPrefixes(ci.body, out);
  for (const auto* s : stmt->fork_stmts) CollectStmtLhsPrefixes(s, out);
}

static void CollectCallNamesExpr(
    const Expr* expr, std::unordered_set<std::string_view>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty())
    out.insert(expr->callee);
  CollectCallNamesExpr(expr->lhs, out);
  CollectCallNamesExpr(expr->rhs, out);
  CollectCallNamesExpr(expr->condition, out);
  CollectCallNamesExpr(expr->true_expr, out);
  CollectCallNamesExpr(expr->false_expr, out);
  CollectCallNamesExpr(expr->base, out);
  CollectCallNamesExpr(expr->index, out);
  for (auto* arg : expr->args) CollectCallNamesExpr(arg, out);
  for (auto* elem : expr->elements) CollectCallNamesExpr(elem, out);
}

static void CollectCallNamesStmt(
    const Stmt* stmt, std::unordered_set<std::string_view>& out) {
  if (!stmt) return;
  CollectCallNamesExpr(stmt->expr, out);
  CollectCallNamesExpr(stmt->rhs, out);
  CollectCallNamesExpr(stmt->condition, out);
  CollectCallNamesExpr(stmt->for_cond, out);
  for (const auto* s : stmt->stmts) CollectCallNamesStmt(s, out);
  CollectCallNamesStmt(stmt->then_branch, out);
  CollectCallNamesStmt(stmt->else_branch, out);
  CollectCallNamesStmt(stmt->body, out);
  CollectCallNamesStmt(stmt->for_body, out);
  for (auto* fi : stmt->for_inits) CollectCallNamesStmt(fi, out);
  for (auto* fs : stmt->for_steps) CollectCallNamesStmt(fs, out);
  for (const auto& ci : stmt->case_items) CollectCallNamesStmt(ci.body, out);
  for (const auto* s : stmt->fork_stmts) CollectCallNamesStmt(s, out);
}

static void CollectFuncLhsPrefixes(
    const Stmt* body, const FuncMap& funcs,
    std::unordered_set<std::string>& out) {
  std::unordered_set<std::string_view> pending;
  CollectCallNamesStmt(body, pending);
  std::unordered_set<std::string_view> visited;
  while (!pending.empty()) {
    std::unordered_set<std::string_view> next;
    for (auto& name : pending) {
      if (visited.count(name)) continue;
      visited.insert(name);
      auto it = funcs.find(name);
      if (it == funcs.end()) continue;
      for (auto* s : it->second->func_body_stmts) {
        CollectStmtLhsPrefixes(s, out);
        CollectCallNamesStmt(s, next);
      }
    }
    pending = std::move(next);
  }
}

static bool PrefixesOverlap(const std::string& a, const std::string& b) {
  if (a == b) return true;
  if (a.size() < b.size())
    return b.compare(0, a.size(), a) == 0 &&
           (b[a.size()] == '.' || b[a.size()] == '[');
  if (b.size() < a.size())
    return a.compare(0, b.size(), b) == 0 &&
           (a[b.size()] == '.' || a[b.size()] == '[');
  return false;
}

struct ProcInfo {
  SourceLoc loc;
  std::unordered_set<std::string> lhs;
  ModuleItemKind kind;
};

static const char* ProcessKindLabel(ModuleItemKind k) {
  switch (k) {
    case ModuleItemKind::kAlwaysFFBlock:
      return "always_ff";
    case ModuleItemKind::kAlwaysLatchBlock:
      return "always_latch";
    default:
      return "always_comb";
  }
}

static void CollectProcessLhsInfo(
    const ModuleDecl* decl, std::vector<ProcInfo>& procs,
    std::unordered_set<std::string>& cont_assign_lhs,
    const FuncMap* func_map) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock) {
      ProcInfo info;
      info.loc = item->loc;
      info.kind = item->kind;
      CollectStmtLhsPrefixes(item->body, info.lhs);
      if (func_map && !func_map->empty())
        CollectFuncLhsPrefixes(item->body, *func_map, info.lhs);
      procs.push_back(std::move(info));
    }
    if (item->kind == ModuleItemKind::kContAssign && item->assign_lhs) {
      std::string prefix = LongestStaticPrefix(item->assign_lhs);
      if (!prefix.empty()) cont_assign_lhs.insert(std::move(prefix));
    }
  }
}

static void CheckMultiProcDriver(const std::string& prefix, size_t i,
                                 const std::vector<ProcInfo>& procs,
                                 DiagEngine& diag) {
  for (size_t j = i + 1; j < procs.size(); ++j) {
    for (const auto& other : procs[j].lhs) {
      if (PrefixesOverlap(prefix, other)) {
        diag.Error(procs[j].loc,
                   std::format("variable '{}' driven by multiple "
                               "always_comb/always_latch/always_ff "
                               "processes",
                               prefix));
        break;
      }
    }
  }
}

static void CheckDriverConflicts(
    const std::vector<ProcInfo>& procs,
    const std::unordered_set<std::string>& cont_assign_lhs, DiagEngine& diag) {
  for (size_t i = 0; i < procs.size(); ++i) {
    for (const auto& var : procs[i].lhs) {
      for (const auto& ca : cont_assign_lhs) {
        if (PrefixesOverlap(var, ca)) {
          diag.Error(procs[i].loc,
                     std::format("variable '{}' driven by {} and "
                                 "continuous assignment",
                                 var, ProcessKindLabel(procs[i].kind)));
          break;
        }
      }
      CheckMultiProcDriver(var, i, procs, diag);
    }
  }
}

// §9.2.2.2, §9.2.2.4: Check that always_comb/always_latch/always_ff LHS
// variables are not driven by other processes or continuous assignments.
void Elaborator::CheckAlwaysCombMultiDriver(const ModuleDecl* decl,
                                            RtlirModule* /*mod*/) {
  std::vector<ProcInfo> procs;
  std::unordered_set<std::string> cont_assign_lhs;
  CollectProcessLhsInfo(decl, procs, cont_assign_lhs, &func_decls_);
  CheckDriverConflicts(procs, cont_assign_lhs, diag_);
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
    var.is_wildcard_index = (t == "*");
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
    const std::unordered_set<std::string_view>& class_names,
    DiagEngine& diag, SourceLoc loc) {
  if (dims.empty() || !dims[0]) return;
  auto* dim = dims[0];
  if (TryParseQueueDim(dim, var, diag, loc)) return;
  if (TryParseAssocDim(dim, var)) return;
  // §7.8.3/§7.8.5: User-defined type (class, struct, enum) as assoc index.
  if (dim->kind == ExprKind::kIdentifier &&
      IsUserDefinedType(dim->text, typedefs, class_names)) {
    var.is_assoc = true;
    // §7.8.3: Mark class-indexed associative arrays.
    if (class_names.count(dim->text) > 0) {
      var.is_class_index = true;
      var.assoc_index_class_name = dim->text;
      var.assoc_index_width = 64;  // Class handles are 64-bit.
    } else {
      // §7.8.5: Resolve typedef to compute index width.
      auto it = typedefs.find(dim->text);
      if (it != typedefs.end()) {
        var.assoc_index_width = EvalTypeWidth(it->second, typedefs);
      }
    }
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
  if (ansi_port_names_.count(item->name)) {
    diag_.Error(item->loc,
                std::format("redeclaration of ANSI port '{}'", item->name));
  }
  // §23.2.2.1 R11: A complete port declaration cannot be redeclared.
  if (non_ansi_complete_ports_.count(item->name)) {
    diag_.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name));
  }
  // §23.2.2.1 R12: A partial port declaration allows a net/variable
  // redeclaration only if the vector ranges match.
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
  ValidatePackedDimRange(item->data_type, item->loc);
  // §6.7.1: Validate explicit net data type is 4-state.
  if (!item->data_type.is_interconnect) {
    DataTypeKind k = item->data_type.kind;
    if (k != DataTypeKind::kStruct && k != DataTypeKind::kUnion &&
        k != DataTypeKind::kEnum && k != DataTypeKind::kNamed &&
        DataTypeToNetType(k) == NetType::kWire &&
        k != DataTypeKind::kWire && !Is4stateType(k)) {
      diag_.Error(item->loc, "net data type must be 4-state");
    }
  }
  // §6.7 footnote 16: charge strength shall only be used with trireg.
  if (item->data_type.charge_strength != 0 &&
      net.net_type != NetType::kTrireg) {
    diag_.Error(item->loc,
                "charge strength can only be used with trireg nets");
  }
  net.is_vectored = item->data_type.is_vectored;
  net.is_scalared = item->data_type.is_scalared;
  // §6.7 footnote 16: vectored/scalared requires at least one packed dim.
  if ((item->data_type.is_vectored || item->data_type.is_scalared) &&
      net.width <= 1 && item->data_type.packed_dim_left == nullptr) {
    diag_.Error(item->loc,
                "vectored or scalared requires at least one packed dimension");
  }
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

  // §10.3.4: Drive strength on net decl applies only to scalar nets,
  // except supply0/supply1.
  if ((item->data_type.drive_strength0 != 0 ||
       item->data_type.drive_strength1 != 0) &&
      net.width > 1 && net.net_type != NetType::kSupply0 &&
      net.net_type != NetType::kSupply1) {
    diag_.Error(item->loc,
                "drive strength on continuous assignment applies only to "
                "scalar nets");
  }
  // §10.3.1: Net declaration assignment creates an implicit continuous assign.
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

void Elaborator::ValidateVarDeclTypes(ModuleItem* item) {
  // §8.4: Track class-typed variables for operator restriction checks.
  if (item->data_type.kind == DataTypeKind::kNamed &&
      class_names_.count(item->data_type.type_name)) {
    class_var_names_.insert(item->name);
    class_var_types_[item->name] = item->data_type.type_name;
    // §8.25: Using the unadorned name of a parameterized class denotes the
    // default specialization. If any parameter lacks a default, the class has
    // no default specialization and the unadorned name is illegal.
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
    // §8.30.1: weak_reference parameter type T shall be a class type.
    if (item->data_type.type_name == "weak_reference" &&
        !item->data_type.type_params.empty()) {
      const auto& tp = item->data_type.type_params[0];
      if (tp.kind != DataTypeKind::kNamed || !class_names_.count(tp.type_name)) {
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
    ValidatePackedUnion(item->data_type, item->loc);
  }
  ValidatePackedDimOnPredefinedType(item->data_type, item->loc);
  ValidateAssocIndexType(item);
}

void Elaborator::TrackVarArrayInfo(const ModuleItem* item,
                                   const RtlirVariable& var) {
  if (item->unpacked_dims.empty()) return;
  VarArrayInfo info{item->data_type.kind,
                    var.unpacked_size,
                    static_cast<uint32_t>(item->unpacked_dims.size()),
                    var.width,
                    var.is_dynamic,
                    var.is_assoc,
                    {},
                    {}};
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
      if (sv && *sv > 0)
        info.dim_sizes.push_back(static_cast<uint32_t>(*sv));
    }
  }
  var_array_info_[item->name] = info;
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
    nettype_net_names_.insert(item->name);
    ElaborateNetDecl(item, mod);
    // §6.6.7: Tag the RtlirNet with user-nettype info.
    auto& net = mod->nets.back();
    net.is_user_nettype = true;
    auto it = nettype_resolve_funcs_.find(item->data_type.type_name);
    if (it != nettype_resolve_funcs_.end()) {
      net.resolve_func = it->second;
    }
    return;
  }
  // §6.8 footnote 14: automatic is illegal in a non-procedural data_declaration.
  if (item->is_automatic) {
    diag_.Error(item->loc,
                "automatic lifetime is not allowed on module-level variables");
  }
  if (ansi_port_names_.count(item->name)) {
    diag_.Error(item->loc,
                std::format("redeclaration of ANSI port '{}'", item->name));
  }
  // §23.2.2.1 R11: A complete port declaration cannot be redeclared.
  if (non_ansi_complete_ports_.count(item->name)) {
    diag_.Error(
        item->loc,
        std::format("redeclaration of port '{}' that has a complete port "
                    "declaration",
                    item->name));
  }
  // §23.2.2.1 R12: A partial port declaration allows a variable
  // redeclaration only if the vector ranges match.
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
  if (!item->data_type.packed_dim_left)
    scalar_var_names_.insert(item->name);
  if (item->data_type.kind == DataTypeKind::kNamed)
    var_named_types_[item->name] = item->data_type.type_name;
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
  var.elem_type_kind = item->data_type.kind;
  var.init_expr = item->init_expr;
  // §10.3.2: Track variables with initializers.
  if (item->init_expr) {
    var_init_names_.insert(item->name);
  }
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
  ComputeUnpackedDims(item->unpacked_dims, var, typedefs_, class_names_,
                      diag_, item->loc);
  ValidateUnpackedDimRange(item->unpacked_dims, item->loc);
  InferDynArraySize(item->unpacked_dims, item->init_expr, var);
  // §7.6/§7.9.9: Track array info for assignment compatibility.
  TrackVarArrayInfo(item, var);
  // §5.12: Resolve attributes.
  var.attrs = ResolveAttributes(item->attrs, diag_);
  mod->variables.push_back(var);
  ValidateArrayInitPattern(item);
  ValidateStructInitPattern(item);
  TrackEnumVariable(item);
  ValidateVarDeclTypes(item);
}

}  // namespace delta
