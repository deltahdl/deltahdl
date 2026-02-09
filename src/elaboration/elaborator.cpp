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
  return (it != unit_->modules.end()) ? *it : nullptr;
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
      RtlirNet net;
      net.name = ScopedName(item->name);
      net.net_type = NetType::kWire;
      net.width = EvalTypeWidth(item->data_type, typedefs_);
      mod->nets.push_back(net);
      break;
    }
    case ModuleItemKind::kVarDecl: {
      RtlirVariable var;
      var.name = ScopedName(item->name);
      var.width = EvalTypeWidth(item->data_type, typedefs_);
      var.is_4state = Is4stateType(item->data_type, typedefs_);
      var.is_event = (item->data_type.kind == DataTypeKind::kEvent);
      mod->variables.push_back(var);
      break;
    }
    case ModuleItemKind::kContAssign: {
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
    case ModuleItemKind::kDefparam:
    case ModuleItemKind::kImportDecl:
    case ModuleItemKind::kExportDecl:
    case ModuleItemKind::kAlias:
      break;
  }
}

void Elaborator::ElaborateTypedef(ModuleItem* item, RtlirModule* mod) {
  typedefs_[item->name] = item->typedef_type;
  if (item->typedef_type.kind != DataTypeKind::kEnum) return;
  int64_t next_val = 0;
  for (const auto& member : item->typedef_type.enum_members) {
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
  for (auto* item : decl->items) {
    ElaborateItem(item, mod);
  }
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

}  // namespace delta
