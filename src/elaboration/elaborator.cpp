#include "elaboration/elaborator.h"

#include <algorithm>
#include <format>
#include <optional>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaboration/const_eval.h"
#include "elaboration/rtlir.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "parser/ast.h"

namespace delta {

Elaborator::Elaborator(Arena& arena, DiagEngine& diag, CompilationUnit* unit)
    : arena_(arena), diag_(diag), unit_(unit) {}

RtlirDesign* Elaborator::Elaborate(std::string_view top_module_name) {
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
  return design;
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

static uint32_t LookupLhsWidth(const Expr* lhs, const RtlirModule* mod) {
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
                       RtlirModule* mod, Arena& arena) {
  RtlirProcess proc;
  proc.kind = kind;
  proc.body = item->body;
  proc.sensitivity = item->sensitivity;
  bool needs_infer = (kind == RtlirProcessKind::kAlwaysComb ||
                      kind == RtlirProcessKind::kAlwaysLatch);
  if (needs_infer && proc.sensitivity.empty()) {
    proc.sensitivity = InferSensitivity(proc.body, arena);
  }
  mod->processes.push_back(proc);
}

// --- Gate elaboration helpers ---

/// Build a binary expression tree from left-folding the given operand over
/// all inputs with the given operator.
static Expr* BuildBinaryChain(Arena& arena, TokenKind op,
                              const std::vector<Expr*>& inputs) {
  Expr* result = inputs[0];
  for (size_t i = 1; i < inputs.size(); ++i) {
    auto* bin = arena.Create<Expr>();
    bin->kind = ExprKind::kBinary;
    bin->op = op;
    bin->lhs = result;
    bin->rhs = inputs[i];
    result = bin;
  }
  return result;
}

/// Wrap an expression in a unary NOT (~).
static Expr* WrapInvert(Arena& arena, Expr* inner) {
  auto* inv = arena.Create<Expr>();
  inv->kind = ExprKind::kUnary;
  inv->op = TokenKind::kTilde;
  inv->lhs = inner;
  return inv;
}

/// Create an integer literal expression with the given value.
static Expr* MakeIntLiteral(Arena& arena, uint64_t val) {
  auto* lit = arena.Create<Expr>();
  lit->kind = ExprKind::kIntegerLiteral;
  lit->int_val = val;
  return lit;
}

/// Build the RHS expression for an N-input gate (and/nand/or/nor/xor/xnor).
static Expr* BuildNInputGateExpr(Arena& arena, GateKind kind,
                                 const std::vector<Expr*>& terminals) {
  // terminals[0] = output, terminals[1..n-1] = inputs.
  std::vector<Expr*> inputs(terminals.begin() + 1, terminals.end());
  TokenKind op = TokenKind::kAmp;
  bool invert = false;
  switch (kind) {
    case GateKind::kAnd:
      op = TokenKind::kAmp;
      break;
    case GateKind::kNand:
      op = TokenKind::kAmp;
      invert = true;
      break;
    case GateKind::kOr:
      op = TokenKind::kPipe;
      break;
    case GateKind::kNor:
      op = TokenKind::kPipe;
      invert = true;
      break;
    case GateKind::kXor:
      op = TokenKind::kCaret;
      break;
    case GateKind::kXnor:
      op = TokenKind::kCaret;
      invert = true;
      break;
    default:
      break;
  }
  auto* chain = BuildBinaryChain(arena, op, inputs);
  return invert ? WrapInvert(arena, chain) : chain;
}

/// Build RHS for buf/not/bufif/notif/pull gates.
static Expr* BuildOutputGateExpr(Arena& arena, GateKind kind,
                                 const std::vector<Expr*>& terminals) {
  switch (kind) {
    case GateKind::kBuf:
      return (terminals.size() >= 2) ? terminals.back() : nullptr;
    case GateKind::kNot:
      return (terminals.size() >= 2) ? WrapInvert(arena, terminals.back())
                                     : nullptr;
    case GateKind::kPullup:
      return MakeIntLiteral(arena, 1);
    case GateKind::kPulldown:
      return MakeIntLiteral(arena, 0);
    default:
      return nullptr;
  }
}

/// Elaborate a gate instance into one or more continuous assigns.
static void ElaborateGateInst(ModuleItem* item, RtlirModule* mod,
                              Arena& arena) {
  auto kind = item->gate_kind;
  auto& terms = item->gate_terminals;
  if (terms.empty()) return;

  Expr* rhs = nullptr;
  switch (kind) {
    case GateKind::kAnd:
    case GateKind::kNand:
    case GateKind::kOr:
    case GateKind::kNor:
    case GateKind::kXor:
    case GateKind::kXnor:
      rhs = BuildNInputGateExpr(arena, kind, terms);
      break;
    default:
      rhs = BuildOutputGateExpr(arena, kind, terms);
      break;
  }

  if (!rhs) return;

  RtlirContAssign ca;
  ca.lhs = terms[0];
  ca.rhs = rhs;
  ca.width = LookupLhsWidth(ca.lhs, mod);
  mod->assigns.push_back(ca);
}

void Elaborator::ElaborateItem(ModuleItem* item, RtlirModule* mod) {
  switch (item->kind) {
    case ModuleItemKind::kNetDecl: {
      if (!declared_names_.insert(item->name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'", item->name));
      }
      var_types_[item->name] = item->data_type.kind;
      RtlirNet net;
      net.name = ScopedName(item->name);
      net.net_type = NetType::kWire;
      net.width = EvalTypeWidth(item->data_type, typedefs_);
      mod->nets.push_back(net);
      break;
    }
    case ModuleItemKind::kVarDecl: {
      if (!declared_names_.insert(item->name).second) {
        diag_.Error(item->loc,
                    std::format("redeclaration of '{}'", item->name));
      }
      var_types_[item->name] = item->data_type.kind;
      RtlirVariable var;
      var.name = ScopedName(item->name);
      var.width = EvalTypeWidth(item->data_type, typedefs_);
      var.is_4state = Is4stateType(item->data_type, typedefs_);
      var.is_event = (item->data_type.kind == DataTypeKind::kEvent);
      mod->variables.push_back(var);
      ValidateArrayInitPattern(item);
      TrackEnumVariable(item);
      if (item->data_type.kind == DataTypeKind::kEnum) {
        ValidateEnumDecl(item->data_type, item->loc);
      }
      break;
    }
    case ModuleItemKind::kContAssign: {
      if (item->assign_lhs && item->assign_lhs->kind == ExprKind::kIdentifier) {
        auto name = item->assign_lhs->text;
        auto [it, ok] = cont_assign_targets_.emplace(name, item->loc);
        if (!ok) {
          diag_.Error(
              item->loc,
              std::format("multiple continuous assignments to '{}'", name));
        }
      }
      RtlirContAssign ca;
      ca.lhs = item->assign_lhs;
      ca.rhs = item->assign_rhs;
      ca.width = LookupLhsWidth(ca.lhs, mod);
      mod->assigns.push_back(ca);
      break;
    }
    case ModuleItemKind::kInitialBlock:
      AddProcess(RtlirProcessKind::kInitial, item, mod, arena_);
      break;
    case ModuleItemKind::kFinalBlock:
      AddProcess(RtlirProcessKind::kFinal, item, mod, arena_);
      break;
    case ModuleItemKind::kAlwaysBlock:
    case ModuleItemKind::kAlwaysCombBlock:
    case ModuleItemKind::kAlwaysFFBlock:
    case ModuleItemKind::kAlwaysLatchBlock:
      AddProcess(MapAlwaysKind(item->always_kind), item, mod, arena_);
      break;
    case ModuleItemKind::kModuleInst:
      ElaborateModuleInst(item, mod);
      break;
    case ModuleItemKind::kParamDecl:
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
    case ModuleItemKind::kFunctionDecl:
    case ModuleItemKind::kTaskDecl:
      mod->function_decls.push_back(item);
      break;
    case ModuleItemKind::kGateInst:
      ElaborateGateInst(item, mod, arena_);
      break;
    case ModuleItemKind::kSpecparam:
      specparam_names_.insert(item->name);
      break;
    case ModuleItemKind::kDefparam:
    case ModuleItemKind::kImportDecl:
    case ModuleItemKind::kExportDecl:
    case ModuleItemKind::kAlias:
    case ModuleItemKind::kPropertyDecl:
    case ModuleItemKind::kSequenceDecl:
    case ModuleItemKind::kAssertProperty:
    case ModuleItemKind::kAssumeProperty:
    case ModuleItemKind::kCoverProperty:
    case ModuleItemKind::kClockingBlock:
    case ModuleItemKind::kCovergroupDecl:
    case ModuleItemKind::kSpecifyBlock:
    case ModuleItemKind::kDpiImport:
    case ModuleItemKind::kDpiExport:
      break;
  }
}

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  typedefs_[item->name] = item->typedef_type;
  if (item->typedef_type.kind != DataTypeKind::kEnum) return;
  ValidateEnumDecl(item->typedef_type, item->loc);
  int64_t next_val = 0;
  for (const auto& member : item->typedef_type.enum_members) {
    enum_member_names_.insert(member.name);
    if (member.value) {
      next_val = ConstEvalInt(member.value).value_or(next_val);
    }
    RtlirVariable var;
    var.name = member.name;
    var.width = EvalTypeWidth(item->typedef_type, typedefs_);
    var.is_4state = false;
    mod->variables.push_back(var);
    ++next_val;
  }
}

void Elaborator::ElaborateItems(const ModuleDecl* decl, RtlirModule* mod) {
  declared_names_.clear();
  cont_assign_targets_.clear();
  proc_assign_targets_.clear();
  var_types_.clear();
  specparam_names_.clear();
  enum_var_names_.clear();
  enum_member_names_.clear();
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
  BindPorts(inst, item);
  mod->children.push_back(inst);
}

void Elaborator::BindPorts(RtlirModuleInst& inst, const ModuleItem* item) {
  if (!inst.resolved) return;
  const auto& child_ports = inst.resolved->ports;

  for (const auto& [port_name, conn_expr] : item->inst_ports) {
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

// --- Defparam resolution ---

/// Collect path components from a member-access chain (a.b.c -> [a, b, c]).
static void CollectPathComponents(const Expr* expr,
                                  std::vector<std::string_view>& out) {
  if (expr->kind == ExprKind::kMemberAccess) {
    CollectPathComponents(expr->lhs, out);
    out.push_back(expr->rhs->text);
    return;
  }
  if (expr->kind == ExprKind::kIdentifier) {
    out.push_back(expr->text);
  }
}

RtlirParamDecl* Elaborator::ResolveDefparamPath(RtlirModule* root,
                                                const Expr* path_expr) {
  std::vector<std::string_view> parts;
  CollectPathComponents(path_expr, parts);
  if (parts.size() < 2) return nullptr;

  // Walk hierarchy: parts[0..n-2] are instance names, parts[n-1] is param.
  RtlirModule* cur = root;
  for (size_t i = 0; i + 1 < parts.size(); ++i) {
    bool found = false;
    for (auto& child : cur->children) {
      if (child.inst_name == parts[i] && child.resolved) {
        cur = child.resolved;
        found = true;
        break;
      }
    }
    if (!found) return nullptr;
  }

  auto param_name = parts.back();
  for (auto& p : cur->params) {
    if (p.name == param_name) return &p;
  }
  return nullptr;
}

void Elaborator::ApplyDefparams(RtlirModule* top, const ModuleDecl* decl) {
  ScopeMap scope = BuildParamScope(top);
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kDefparam) continue;
    for (const auto& [path_expr, val_expr] : item->defparam_assigns) {
      auto* param = ResolveDefparamPath(top, path_expr);
      if (!param) {
        diag_.Warning(item->loc, "defparam target not found");
        continue;
      }
      if (param->from_override) continue;  // Instance #(...) takes priority.
      auto val = ConstEvalInt(val_expr, scope);
      if (!val) {
        diag_.Warning(item->loc, "defparam value is not constant");
        continue;
      }
      param->resolved_value = *val;
      param->is_resolved = true;
    }
  }
}

void Elaborator::ValidateArrayInitPattern(const ModuleItem* item) {
  if (!item->init_expr || item->unpacked_dims.empty()) return;
  if (item->init_expr->kind != ExprKind::kAssignmentPattern) return;
  if (item->init_expr->repeat_count) return;           // replication form
  if (!item->init_expr->pattern_keys.empty()) return;  // named form

  const auto* dim = item->unpacked_dims[0];
  if (!dim) return;  // dynamic array

  std::optional<int64_t> dim_size;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto left = ConstEvalInt(dim->lhs);
    auto right = ConstEvalInt(dim->rhs);
    if (left && right) {
      dim_size = std::abs(*left - *right) + 1;
    }
  } else {
    dim_size = ConstEvalInt(dim);
  }
  if (!dim_size) return;

  auto count = static_cast<int64_t>(item->init_expr->elements.size());
  if (count != *dim_size) {
    diag_.Error(item->loc,
                std::format("assignment pattern has {} elements, but array "
                            "dimension requires {}",
                            count, *dim_size));
  }
}

// --- §6 validation helpers ---

static std::string_view ExprIdent(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kIdentifier) return e->text;
  return {};
}

static void CollectProcTargets(const Stmt* s,
                               std::unordered_set<std::string_view>& out) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    auto name = ExprIdent(s->lhs);
    if (!name.empty()) out.insert(name);
  }
  for (auto* sub : s->stmts) CollectProcTargets(sub, out);
  CollectProcTargets(s->then_branch, out);
  CollectProcTargets(s->else_branch, out);
  CollectProcTargets(s->body, out);
  CollectProcTargets(s->for_body, out);
  for (auto& ci : s->case_items) CollectProcTargets(ci.body, out);
}

static bool IsRealType(DataTypeKind k) {
  return k == DataTypeKind::kReal || k == DataTypeKind::kShortreal ||
         k == DataTypeKind::kRealtime;
}

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

static void CheckRealSelectNode(const Expr* e, const TypeMap& types,
                                DiagEngine& diag) {
  auto name = ExprIdent(e->base);
  if (!name.empty()) {
    auto it = types.find(name);
    if (it != types.end() && IsRealType(it->second)) {
      diag.Error(e->range.start, "bit-select on real type is illegal");
      return;
    }
  }
  if (!e->index) return;
  auto idx = ExprIdent(e->index);
  if (idx.empty()) return;
  auto it = types.find(idx);
  if (it != types.end() && IsRealType(it->second)) {
    diag.Error(e->range.start, "real type used as index is illegal");
  }
}

static void CheckRealSelect(const Expr* e, const TypeMap& types,
                            DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kSelect && e->base) {
    CheckRealSelectNode(e, types, diag);
  }
  CheckRealSelect(e->lhs, types, diag);
  CheckRealSelect(e->rhs, types, diag);
  CheckRealSelect(e->base, types, diag);
  CheckRealSelect(e->index, types, diag);
}

static bool ExprContainsIdent(const Expr* e, std::string_view name) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == name) return true;
  if (ExprContainsIdent(e->lhs, name)) return true;
  return ExprContainsIdent(e->rhs, name);
}

void Elaborator::ValidateEdgeOnReal(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kAlwaysBlock) return;
  for (const auto& ev : item->sensitivity) {
    if (ev.edge == Edge::kNone) continue;
    auto name = ExprIdent(ev.signal);
    if (name.empty()) continue;
    auto it = var_types_.find(name);
    if (it != var_types_.end() && IsRealType(it->second)) {
      diag_.Error(item->loc, "edge event on real type is illegal");
    }
  }
}

void Elaborator::ValidateItemConstraints(const ModuleItem* item) {
  bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                 item->kind == ModuleItemKind::kInitialBlock;
  if (is_proc && item->body) {
    CollectProcTargets(item->body, proc_assign_targets_);
  }
  ValidateEdgeOnReal(item);
  if (item->kind == ModuleItemKind::kContAssign) {
    CheckRealSelect(item->assign_rhs, var_types_, diag_);
  }
}

void Elaborator::ValidateMixedAssignments() {
  for (const auto& [name, loc] : cont_assign_targets_) {
    if (proc_assign_targets_.count(name) != 0) {
      diag_.Error(loc, std::format("variable '{}' has both continuous and "
                                   "procedural assignments",
                                   name));
    }
  }
}

void Elaborator::ValidateSpecparamInParams(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kParamDecl) continue;
    if (!item->init_expr) continue;
    for (const auto& sp : specparam_names_) {
      if (ExprContainsIdent(item->init_expr, sp)) {
        diag_.Error(item->loc,
                    std::format("parameter references specparam '{}'", sp));
        break;
      }
    }
  }
}

void Elaborator::ValidateModuleConstraints(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    ValidateItemConstraints(item);
  }
  ValidateMixedAssignments();
  ValidateSpecparamInParams(decl);
  ValidateEnumAssignments(decl);
}

// §6.19 enum validation helpers

static int64_t ParseLiteralWidth(std::string_view txt) {
  auto apos = txt.find('\'');
  if (apos == std::string_view::npos || apos == 0) return 0;
  int64_t width = 0;
  for (size_t i = 0; i < apos; ++i) {
    if (txt[i] < '0' || txt[i] > '9') return 0;
    width = width * 10 + (txt[i] - '0');
  }
  return width;
}

static bool LiteralHasXZ(std::string_view txt) {
  auto apos = txt.find('\'');
  if (apos == std::string_view::npos) return false;
  return txt.substr(apos + 1).find_first_of("xXzZ") != std::string_view::npos;
}

static bool ExprContainsXZ(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kIntegerLiteral && LiteralHasXZ(e->text)) {
    return true;
  }
  if (ExprContainsXZ(e->lhs)) return true;
  if (ExprContainsXZ(e->rhs)) return true;
  for (const auto* elem : e->elements) {
    if (ExprContainsXZ(elem)) return true;
  }
  return ExprContainsXZ(e->repeat_count);
}

bool Elaborator::ValidateEnumLiteral(const EnumMember& member,
                                     uint32_t base_width, bool is_2state) {
  if (member.value->kind == ExprKind::kIntegerLiteral) {
    auto width = ParseLiteralWidth(member.value->text);
    if (width > 0) {
      if (width != static_cast<int64_t>(base_width)) {
        diag_.Error(member.value->range.start,
                    std::format("enum literal width {} does not match "
                                "base type width {}",
                                width, base_width));
      }
    }
  }
  bool has_xz = ExprContainsXZ(member.value);
  if (has_xz && is_2state) {
    diag_.Error(member.value->range.start,
                "x/z value in 2-state enum is illegal");
  }
  return has_xz;
}

void Elaborator::ValidateEnumDecl(const DataType& dtype, SourceLoc loc) {
  auto base_width = EvalTypeWidth(dtype, typedefs_);
  bool is_2state = !Is4stateType(dtype, typedefs_);
  bool prev_had_xz = false;

  for (const auto& member : dtype.enum_members) {
    if (!member.value) {
      if (prev_had_xz) {
        diag_.Error(loc,
                    std::format("unassigned enum member '{}' follows member "
                                "with x/z value",
                                member.name));
      }
      prev_had_xz = false;
      continue;
    }
    prev_had_xz = ValidateEnumLiteral(member, base_width, is_2state);
  }
}

// §6.19.3/§6.19.4 enum assignment validation

void Elaborator::TrackEnumVariable(const ModuleItem* item) {
  if (item->data_type.kind == DataTypeKind::kEnum) {
    enum_var_names_.insert(item->name);
    for (const auto& m : item->data_type.enum_members) {
      enum_member_names_.insert(m.name);
    }
    return;
  }
  if (item->data_type.kind != DataTypeKind::kNamed) return;
  auto it = typedefs_.find(item->data_type.type_name);
  if (it != typedefs_.end() && it->second.kind == DataTypeKind::kEnum) {
    enum_var_names_.insert(item->name);
  }
}

static bool IsCompoundAssignOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

void Elaborator::CheckEnumAssignStmt(const Stmt* s) {
  auto name = ExprIdent(s->lhs);
  if (name.empty()) return;
  if (enum_var_names_.count(name) == 0) return;
  if (s->rhs && s->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(s->rhs->op)) {
    diag_.Error(s->range.start,
                "compound assignment to enum variable without cast");
    return;
  }
  if (!s->rhs) return;
  if (s->rhs->kind == ExprKind::kIdentifier) return;
  if (s->rhs->kind == ExprKind::kCast) return;
  diag_.Error(s->range.start, "integer assigned to enum variable without cast");
}

void Elaborator::WalkStmtsForEnumAssign(const Stmt* s) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl) {
    if (s->var_decl_type.kind == DataTypeKind::kNamed) {
      auto it = typedefs_.find(s->var_decl_type.type_name);
      if (it != typedefs_.end() && it->second.kind == DataTypeKind::kEnum) {
        enum_var_names_.insert(s->var_name);
      }
    }
  }
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    CheckEnumAssignStmt(s);
  }
  for (auto* sub : s->stmts) WalkStmtsForEnumAssign(sub);
  WalkStmtsForEnumAssign(s->then_branch);
  WalkStmtsForEnumAssign(s->else_branch);
  WalkStmtsForEnumAssign(s->body);
  WalkStmtsForEnumAssign(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForEnumAssign(ci.body);
}

void Elaborator::ValidateEnumAssignments(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForEnumAssign(item->body);
    }
  }
}

}  // namespace delta
