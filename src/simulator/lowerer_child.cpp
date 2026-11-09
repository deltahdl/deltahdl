#include "simulator/lowerer_child.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_alias.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/class_object.h"
#include "simulator/disable_scope.h"
#include "simulator/dpi_export.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/switch_network.h"
#include "simulator/unit_scope_items.h"
#include "simulator/variable.h"

namespace delta {

void Lowerer::CreateChildModuleVariables(const std::string& inst_prefix,
                                         const RtlirModule* resolved) {
  for (const auto& var : resolved->variables) {
    auto* name =
        arena_.Create<std::string>(inst_prefix + std::string(var.name));
    LowerVar(*name, var);
  }
}

static void CreateChildModulePorts(const std::string& inst_prefix,
                                   const RtlirModule* resolved, SimContext& ctx,
                                   Arena& arena) {
  for (const auto& port : resolved->ports) {
    CreatePortStorage(inst_prefix, port, ctx, arena);
  }
}

static bool NetNamesAPortOf(const RtlirModule* mod, std::string_view name) {
  for (const auto& port : mod->ports) {
    if (port.name == name) return true;
  }
  return false;
}

static bool ChildOwnsNet(const RtlirModuleInst& child, const RtlirNet& net) {
  const RtlirModule* resolved = child.resolved;
  if (resolved->is_interface) return true;
  if (NetNamesAPortOf(resolved, net.name)) return false;
  return !net.refers_outward;
}

static void CreateChildModuleNets(const std::string& inst_prefix,
                                  const RtlirModuleInst& child, SimContext& ctx,
                                  Arena& arena) {
  const RtlirModule* resolved = child.resolved;
  for (const auto& net : resolved->nets) {
    if (!ChildOwnsNet(child, net)) continue;
    auto* name = arena.Create<std::string>(inst_prefix + std::string(net.name));
    CreateDeclaredNet(*name, net, resolved->timescale, ctx, arena);
  }
}

struct AliasBit {
  Net* net;
  uint32_t offset;
};

static std::optional<std::pair<int64_t, int64_t>> AliasSelectOffsets(
    const Expr* sel, const Variable& var, SimContext& ctx, Arena& arena) {
  auto value = [&](const Expr* e) {
    return SelectBoundValue(EvalExpr(e, ctx, arena));
  };
  int64_t first = value(sel->index);
  int64_t second = first;
  if (sel->is_part_select_plus || sel->is_part_select_minus) {
    int64_t width = value(sel->index_end);
    second = sel->is_part_select_plus ? first + width - 1 : first - width + 1;
  } else if (sel->index_end != nullptr) {
    second = value(sel->index_end);
  }
  PackedRange range = var.DeclaredRange();
  if (!range.Contains(first) || !range.Contains(second)) return std::nullopt;
  int64_t a = range.OffsetOf(first);
  int64_t b = range.OffsetOf(second);
  return std::make_pair(std::min(a, b), std::max(a, b));
}

struct AliasScope {
  const std::string& inst_prefix;
  const GenBlockPrefixes& gen_blocks;
};

std::string GenBlockObjectKey(const std::string& inst_prefix,
                              const GenBlockPrefixes& gen_blocks,
                              std::string_view name, SimContext& ctx) {
  for (auto it = gen_blocks.rbegin(); it != gen_blocks.rend(); ++it) {
    std::string key = inst_prefix + std::string(*it) + std::string(name);
    if (ctx.FindVariable(key) != nullptr) return key;
  }
  return inst_prefix + std::string(name);
}

static bool AppendNetOperandBits(const Expr* e, const AliasScope& scope,
                                 SimContext& ctx, Arena& arena,
                                 std::vector<AliasBit>& out) {
  const Expr* base = e->kind == ExprKind::kSelect ? e->base : e;
  if (base == nullptr || base->kind != ExprKind::kIdentifier) return false;
  Net* net = ctx.FindNet(
      GenBlockObjectKey(scope.inst_prefix, scope.gen_blocks, base->text, ctx));
  if (net == nullptr || net->resolved == nullptr) return false;
  std::pair<int64_t, int64_t> span{0, net->resolved->value.width - 1};
  if (e->kind == ExprKind::kSelect) {
    auto offsets = AliasSelectOffsets(e, *net->resolved, ctx, arena);
    if (!offsets) return false;
    span = *offsets;
  }
  for (int64_t off = span.second; off >= span.first; --off)
    out.push_back({net, static_cast<uint32_t>(off)});
  return true;
}

static bool AppendAliasBits(const Expr* e, const AliasScope& scope,
                            SimContext& ctx, Arena& arena,
                            std::vector<AliasBit>& out) {
  e = UnwrapTypedPattern(e);
  if (e->kind != ExprKind::kConcatenation &&
      e->kind != ExprKind::kAssignmentPattern)
    return AppendNetOperandBits(e, scope, ctx, arena, out);
  for (const Expr* el : e->elements) {
    if (!AppendAliasBits(el, scope, ctx, arena, out)) return false;
  }
  return true;
}

using AliasBitMap = std::vector<std::pair<uint32_t, uint32_t>>;

static std::map<std::pair<Net*, Net*>, AliasBitMap> JoinedBitMaps(
    const std::vector<std::vector<AliasBit>>& operands) {
  std::map<std::pair<Net*, Net*>, AliasBitMap> maps;
  for (size_t pos = 0; pos < operands.front().size(); ++pos) {
    for (const auto& x : operands) {
      for (const auto& y : operands) {
        if (x[pos].net == y[pos].net) continue;
        maps[{x[pos].net, y[pos].net}].emplace_back(x[pos].offset,
                                                    y[pos].offset);
      }
    }
  }
  return maps;
}

static void JoinOperandBits(const std::vector<std::vector<AliasBit>>& operands,
                            Arena& arena) {
  auto* join = arena.Create<BidirSwitchState>();
  join->state = BidirSwitchState::kOn;
  join->is_alias = true;
  for (auto& [nets, pairs] : JoinedBitMaps(operands)) {
    nets.first->switch_links.push_back(
        {nets.second, join, arena.Create<AliasBitMap>(std::move(pairs))});
  }
}

static void LowerBitAlias(const RtlirAlias& alias, const std::string& prefix,
                          SimContext& ctx, Arena& arena) {
  const AliasScope kScope{prefix, alias.gen_block_prefixes};
  std::vector<std::vector<AliasBit>> operands;
  for (const Expr* e : alias.nets) {
    operands.emplace_back();
    if (!AppendAliasBits(e, kScope, ctx, arena, operands.back())) return;
    if (operands.back().size() != operands.front().size()) return;
  }
  JoinOperandBits(operands, arena);
}

void JoinInoutPortBits(const Expr& connection, Net& port_net,
                       const std::string& inst_prefix,
                       const GenBlockPrefixes& gen_blocks, SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  std::vector<AliasBit> outside;
  if (!AppendAliasBits(&connection, AliasScope{inst_prefix, gen_blocks}, ctx,
                       arena, outside)) {
    return;
  }
  std::vector<AliasBit> inside;
  for (uint32_t off = port_net.resolved->value.width; off-- > 0;)
    inside.push_back({&port_net, off});
  const auto kJoined =
      static_cast<std::ptrdiff_t>(std::min(inside.size(), outside.size()));
  inside.erase(inside.begin(), inside.end() - kJoined);
  outside.erase(outside.begin(), outside.end() - kJoined);
  JoinOperandBits({std::move(inside), std::move(outside)}, arena);
  port_net.Resolve(arena, &ctx.GetScheduler());
}

static std::string AliasGroupRoot(
    const std::unordered_map<std::string, std::string>& parent,
    std::string name) {
  for (auto it = parent.find(name); it != parent.end() && it->second != name;
       it = parent.find(name)) {
    name = it->second;
  }
  return name;
}

void Lowerer::LowerAliases(const RtlirModule* mod) {
  std::unordered_map<std::string, std::string> parent;
  for (const auto& alias : mod->aliases) {
    if (alias.nets.size() < 2) continue;
    bool whole_nets = std::all_of(
        alias.nets.begin(), alias.nets.end(),
        [](const Expr* e) { return e->kind == ExprKind::kIdentifier; });
    if (!whole_nets) {
      LowerBitAlias(alias, inst_prefix_, ctx_, arena_);
      continue;
    }
    const AliasScope kScope{inst_prefix_, alias.gen_block_prefixes};
    std::string root = AliasGroupRoot(
        parent, GenBlockObjectKey(kScope.inst_prefix, kScope.gen_blocks,
                                  alias.nets[0]->text, ctx_));
    parent.emplace(root, root);
    for (auto* net : alias.nets) {
      std::string other = AliasGroupRoot(
          parent, GenBlockObjectKey(kScope.inst_prefix, kScope.gen_blocks,
                                    net->text, ctx_));
      parent[other] = root;
    }
  }
  for (const auto& entry : parent) {
    const std::string& member = entry.first;
    std::string root = AliasGroupRoot(parent, member);
    if (root == member) continue;
    const std::string& name = *arena_.Create<std::string>(member);
    const std::string& primary = *arena_.Create<std::string>(root);
    ctx_.AliasVariable(name, primary);
    ctx_.AliasNet(name, primary);
  }
}

std::string Lowerer::ConnectedInstancePath(std::string_view name) const {
  std::string local = inst_prefix_ + std::string(name);
  std::string_view head = name.substr(0, name.find('.'));
  bool rooted = head.size() < name.size() &&
                (ctx_.IsTopModule(head) || ctx_.IsParallelTop(head)) &&
                ctx_.FindInstanceType(local).empty();
  return rooted ? ctx_.RootedStorageKey(name) : local;
}

void Lowerer::LowerParallelTop(const RtlirModule* mod) {
  ctx_.RegisterParallelTop(mod->name);
  RtlirModuleInst inst;
  inst.module_name = mod->name;
  inst.inst_name = mod->name;
  inst.simple_inst_name = mod->name;
  inst.resolved = const_cast<RtlirModule*>(mod);
  LowerChildInstance(inst);
}

static std::string_view ActualHeadName(const Expr* conn) {
  while (conn != nullptr && conn->kind == ExprKind::kMemberAccess) {
    conn = conn->lhs;
  }
  if (conn == nullptr || conn->kind != ExprKind::kIdentifier) return {};
  return conn->text;
}

void Lowerer::LowerTopNamedBy(const Expr* conn) {
  std::string_view text = ActualHeadName(conn);
  std::string_view name = text.substr(0, text.find('.'));
  const auto& tops = design_->top_modules;
  auto top = std::ranges::find(tops, name, &RtlirModule::name);
  if (name.size() == text.size() || top == tops.end() || top == tops.begin() ||
      ctx_.IsParallelTop(name) ||
      !ctx_.FindInstanceType(inst_prefix_ + std::string(name)).empty()) {
    return;
  }
  std::string saved_prefix = std::exchange(inst_prefix_, std::string());
  const RtlirModule* saved_parent = port_parent_;
  LowerParallelTop(*top);
  inst_prefix_ = std::move(saved_prefix);
  port_parent_ = saved_parent;
  ctx_.SetLoweringInstancePrefix(inst_prefix_);
}

static std::string ChildInstanceLevel(const RtlirModuleInst& child) {
  std::string_view simple =
      child.simple_inst_name.empty() ? child.inst_name : child.simple_inst_name;
  std::string level(simple);
  size_t bracket = child.inst_name.rfind('[');
  if (!simple.ends_with(']') && child.inst_name.ends_with(']') &&
      bracket != std::string_view::npos) {
    level += child.inst_name.substr(bracket);
  }
  return level;
}

static std::string RegisterChildInstancePath(const std::string& parent_prefix,
                                             const std::string& child_prefix,
                                             const RtlirModuleInst& child,
                                             SimContext& ctx) {
  std::string path(ctx.FindInstancePath(parent_prefix));
  if (path.empty()) {
    path = parent_prefix;
    if (!path.empty()) path.pop_back();
  }
  std::string gen = GenBlockName(child.gen_block_path);
  std::string own = ChildInstanceLevel(child);
  for (std::string_view level :
       {std::string_view(gen), std::string_view(own)}) {
    if (level.empty()) continue;
    if (!path.empty()) path += '.';
    path += level;
  }
  if (path + "." == child_prefix) return {};
  ctx.RegisterInstancePath(child_prefix, path);
  return path;
}

static void AliasChildObjectsUnderPath(const std::string& child_prefix,
                                       const std::string& path, SimContext& ctx,
                                       Arena& arena) {
  auto under_path = [&](std::string_view key) -> std::string_view {
    return *arena.Create<std::string>(
        path + "." + std::string(key.substr(child_prefix.size())));
  };
  std::vector<std::pair<std::string_view, Variable*>> vars;
  for (const auto& [key, var] : ctx.GetVariables())
    if (key.starts_with(child_prefix)) vars.emplace_back(key, var);
  std::vector<std::string_view> nets;
  for (const auto& [key, net] : ctx.GetNets())
    if (key.starts_with(child_prefix)) nets.push_back(key);
  for (const auto& [key, var] : vars) {
    std::string_view alias = under_path(key);
    ctx.AliasVariable(alias, var);
    AliasVariableKinds(alias, key, ctx, arena);
  }
  for (std::string_view key : nets) ctx.AliasNet(under_path(key), key);
}

void RegisterModuleLets(const RtlirModule* mod, std::string_view prefix,
                        SimContext& ctx) {
  for (auto* item : mod->let_decls) {
    if (item->kind == ModuleItemKind::kCovergroupDecl) {
      ctx.RegisterLetDecl(item->name, item);
    } else {
      RegisterInstanceLet(ctx, prefix, item);
    }
  }
}

static void RegisterChildInstanceDecls(const RtlirModule* mod,
                                       const std::string& prefix,
                                       SimContext& ctx, Arena& arena) {
  RegisterModuleSubroutines(mod, ctx);
  RegisterModuleLets(mod, prefix, ctx);
  RegisterInstanceSubroutines(mod, prefix, ctx, arena);
  RegisterGenBlockSubroutines(mod, prefix, prefix, ctx, arena);
  RegisterModuleDpiImports(mod, ctx);
  RegisterModuleDpiExports(mod, prefix, ctx);
  RegisterModuleSequenceDecls(mod, ctx);
}

void Lowerer::RegisterChildInstanceKeys(const RtlirModule* mod) {
  for (const auto& child : mod->children) {
    if (child.resolved == nullptr) continue;
    RegisterInstanceKeyBinding(inst_prefix_ + std::string(child.inst_name),
                               child.resolved, ctx_);
  }
}

static const RtlirModuleInst* UnplacedInterfaceActual(
    const RtlirModuleInst& child, const std::vector<RtlirModuleInst>& siblings,
    const std::vector<bool>& placed, size_t& index) {
  for (const RtlirPortBinding& binding : child.port_bindings) {
    const Expr* head = binding.connection;
    if (head != nullptr && head->kind == ExprKind::kMemberAccess) {
      head = head->lhs;
    }
    if (head == nullptr || head->kind != ExprKind::kIdentifier) continue;
    std::string_view name = head->text.substr(0, head->text.find('.'));
    bool through_module = name.size() != head->text.size();
    for (index = 0; index < siblings.size(); ++index) {
      const RtlirModuleInst& sibling = siblings[index];
      if (!placed[index] && sibling.resolved != nullptr &&
          (through_module || sibling.resolved->is_interface) &&
          sibling.inst_name == name) {
        return &sibling;
      }
    }
  }
  return nullptr;
}

static void CollectFullPathActuals(const RtlirModuleInst& inst,
                                   const SimContext& ctx,
                                   std::vector<std::string>& paths) {
  for (const RtlirPortBinding& binding : inst.port_bindings) {
    std::string_view text = ActualHeadName(binding.connection);
    std::string_view head = text.substr(0, text.find('.'));
    if (head.size() < text.size() &&
        (ctx.IsTopModule(head) || ctx.IsParallelTop(head))) {
      paths.push_back(ctx.RootedStorageKey(text));
    }
  }
  if (inst.resolved == nullptr) return;
  for (const RtlirModuleInst& child : inst.resolved->children) {
    CollectFullPathActuals(child, ctx, paths);
  }
}

static const RtlirModuleInst* UnplacedPathTarget(
    const std::vector<std::string>& paths, const std::string& prefix,
    const std::vector<RtlirModuleInst>& siblings,
    const std::vector<bool>& placed, size_t& index) {
  for (const std::string& path : paths) {
    if (!path.starts_with(prefix)) continue;
    std::string_view rest = std::string_view(path).substr(prefix.size());
    std::string_view name = rest.substr(0, rest.find('.'));
    for (index = 0; index < siblings.size(); ++index) {
      const RtlirModuleInst& sibling = siblings[index];
      if (!placed[index] && sibling.resolved != nullptr &&
          sibling.inst_name == name) {
        return &sibling;
      }
    }
  }
  return nullptr;
}

void Lowerer::LowerChildModules(const RtlirModule* mod) {
  const std::vector<RtlirModuleInst>& children = mod->children;
  std::vector<bool> placed(children.size(), false);
  for (size_t i = 0; i < children.size(); ++i) {
    if (placed[i] || children[i].resolved == nullptr) continue;
    placed[i] = true;
    std::vector<std::string> paths;
    CollectFullPathActuals(children[i], ctx_, paths);
    size_t index = 0;
    for (;;) {
      const RtlirModuleInst* ahead =
          UnplacedInterfaceActual(children[i], children, placed, index);
      if (ahead == nullptr) {
        ahead =
            UnplacedPathTarget(paths, inst_prefix_, children, placed, index);
      }
      if (ahead == nullptr) break;
      placed[index] = true;
      port_parent_ = mod;
      LowerChildInstance(*ahead);
    }
    port_parent_ = mod;
    LowerChildInstance(children[i]);
  }
}

void Lowerer::LowerChildBody(const RtlirModule* mod) {
  LowerAliases(mod);
  uint32_t child_block_id = mod->is_program ? next_program_block_id_++ : 0;
  LowerSequenceMonitors(mod);
  LowerFreeVariableSolver(mod);
  bool reactive = mod->is_program || mod->is_checker;
  lowering_checker_ = mod->is_checker;
  LowerProcesses(mod->processes, reactive, child_block_id);
  lowering_checker_ = false;
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca, reactive);
  }
  for (const auto& sw : mod->bidir_switches) {
    LowerBidirSwitch(sw, mod->is_program);
  }
  for (const auto& udp_inst : mod->udp_insts) {
    LowerUdpInst(udp_inst, mod->is_program);
  }
  LowerClockingBlocks(mod);

  LowerChildModules(mod);
}

std::vector<const ClassDecl*> Lowerer::RegisterChildClasses(
    const RtlirModule* mod) {
  std::vector<const ClassDecl*> fresh_classes;
  for (auto* cls : mod->class_decls) {
    const ClassTypeInfo* known = ctx_.FindClassType(cls->name);
    const bool kRegistered = known != nullptr && known->decl == cls;
    if (kRegistered && cls->params.empty()) continue;
    const std::string kOuter =
        ctx_.SetClassInstanceScope(kRegistered ? inst_prefix_ : std::string());
    RegisterClassDecl(cls, mod->function_decls);
    ctx_.SetClassInstanceScope(kOuter);
    fresh_classes.push_back(cls);
  }
  return fresh_classes;
}

void RegisterTypeRefCompares(const std::string& inst_prefix,
                             const RtlirModule* mod, SimContext& ctx) {
  for (const TypeRefCompareResult& result : mod->type_ref_compares) {
    ctx.RecordTypeRefCompare(inst_prefix + std::string(result.gen_prefix),
                             result.expr, result.holds);
  }
}

void Lowerer::LowerChildInstance(const RtlirModuleInst& child) {
  for (const RtlirPortBinding& binding : child.port_bindings) {
    LowerTopNamedBy(binding.connection);
  }
  auto saved_prefix = inst_prefix_;
  auto child_prefix = inst_prefix_ + std::string(child.inst_name) + ".";
  std::string child_path =
      RegisterChildInstancePath(saved_prefix, child_prefix, child, ctx_);
  inst_prefix_ = child_prefix;
  EnterInstanceUnit(design_, child.resolved, inst_prefix_, ctx_, arena_);
  instance_prefixes_.try_emplace(child.resolved, inst_prefix_);
  if (child.resolved->is_interface) {
    interface_instance_prefixes_.push_back(child_prefix);
  }
  ctx_.SetLoweringInstancePrefix(inst_prefix_);
  if (child.is_nested_decl) ctx_.RegisterNestedDeclScope(inst_prefix_);

  RegisterInstanceKeyBinding(inst_prefix_, child.resolved, ctx_);
  RegisterTypeRefCompares(inst_prefix_, child.resolved, ctx_);
  LowerParams(child.resolved);
  RecordSpecifyScope(child.resolved);
  LowerImports(child.resolved);
  RegisterEnumTypes(child.resolved);
  RegisterParamEnumTypes(child.resolved);
  std::vector<const ClassDecl*> fresh_classes =
      RegisterChildClasses(child.resolved);
  RegisterChildInstanceKeys(child.resolved);
  CreateChildModuleVariables(inst_prefix_, child.resolved);
  for (const ClassDecl* cls : fresh_classes) InitClassStaticProperties(cls);
  CreateChildModulePorts(inst_prefix_, child.resolved, ctx_, arena_);
  CreateChildModuleNets(inst_prefix_, child, ctx_, arena_);
  RegisterGenBlockMembers(child.resolved);
  if (!child_path.empty())
    AliasChildObjectsUnderPath(child_prefix, child_path, ctx_, arena_);
  RegisterChildInstanceDecls(child.resolved, inst_prefix_, ctx_, arena_);
  RecordSubroutineAssertionSampleScopes(child.resolved);
  RecordStaticLocalSubroutines(child.resolved);
  DeclareModuleNamedScopes(*child.resolved, inst_prefix_, ctx_);

  inst_prefix_ = saved_prefix;
  ctx_.SetLoweringInstancePrefix(inst_prefix_);
  LowerPortBindings(child, child.resolved->is_program);
  inst_prefix_ = child_prefix;
  ctx_.SetLoweringInstancePrefix(inst_prefix_);

  LowerChildBodyUnderCheckerRoot(child);

  inst_prefix_ = saved_prefix;
  ctx_.SetLoweringInstancePrefix(inst_prefix_);
}

}  // namespace delta
