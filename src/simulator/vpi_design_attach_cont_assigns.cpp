#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <memory>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_alias.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_assigns_internal.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_expr_scope.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_pool_keeper.h"
#include "simulator/vpi_source_delay.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

void CollectTargets(const Expr* expr, std::vector<std::string_view>& out) {
  if (expr == nullptr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    out.push_back(expr->text);
  } else if (expr->kind == ExprKind::kSelect) {
    CollectTargets(expr->base, out);
  } else if (expr->kind == ExprKind::kConcatenation) {
    for (const Expr* element : expr->elements) CollectTargets(element, out);
  }
}

}  // namespace

void CollectReads(const Expr* expr, std::vector<std::string_view>& out) {
  if (expr == nullptr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    out.push_back(expr->text);
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    CollectReads(expr->lhs, out);
    return;
  }
  for (const Expr* sub : {expr->lhs, expr->rhs, expr->condition,
                          expr->true_expr, expr->false_expr, expr->base,
                          expr->index, expr->index_end, expr->repeat_count}) {
    CollectReads(sub, out);
  }
  for (const Expr* arg : expr->args) CollectReads(arg, out);
  for (const Expr* element : expr->elements) CollectReads(element, out);
}

namespace {

void HangOn(VpiObject* assign, const std::vector<std::string_view>& found,
            const AssignNames& names) {
  for (std::string_view name : found) {
    VpiHandle net = Resolve(names, name);
    if (net == nullptr) continue;
    bool present = false;
    for (const VpiObject* child : net->children) present |= child == assign;
    if (!present) net->children.push_back(assign);
  }
}

void MakeContAssignBits(VpiObject* assign, const AssignBuild& build) {
  const int kWidth = assign->lhs != nullptr ? assign->lhs->size : 0;
  for (int offset = 0; kWidth > 1 && offset < kWidth; ++offset) {
    VpiObject* bit = build.alloc();
    bit->type = vpiContAssignBit;
    bit->parent = assign;
    bit->index = -1;
    bit->offset = offset;
    bit->bit_offset = offset;
    bit->size = 1;
    bit->expr_scope = assign->expr_scope;
    assign->children.push_back(bit);
  }
}

void MakeContinuousAssignment(const RtlirContAssign& ca, VpiObject* scope,
                              const AssignBuild& build) {
  const ModuleItem* item = ca.source_item;
  const bool kDecl = item->kind == ModuleItemKind::kNetDecl;
  const Expr* lhs = kDecl ? ca.lhs : item->assign_lhs;
  const Expr* rhs = kDecl ? item->init_expr : item->assign_rhs;

  VpiObject* obj = build.alloc();
  obj->type = vpiContAssign;
  obj->index = -1;
  obj->net_decl_assign = kDecl;
  obj->parent = scope;
  scope->children.push_back(obj);
  obj->lhs = ExpressionObject(lhs, build);
  obj->rhs = AssignedExpressionObject(rhs, obj->lhs, build);
  obj->expr_scope = std::make_shared<const VpiExprScope>(VpiExprScope{
      rhs, VpiFlatName(build.names.prefix, ""),
      std::vector<std::string>(build.names.gen.begin(), build.names.gen.end()),
      obj->lhs != nullptr ? static_cast<uint32_t>(obj->lhs->size) : 0U});
  MakeContAssignBits(obj, build);

  if (build.sim != nullptr) {
    VpiFillContAssignDelays(obj, ca, VpiFlatName(build.names.prefix, ""),
                            *build.sim, build.alloc);
    VpiRecordWrittenLocation(obj, item->loc, *build.sim);
  }

  std::vector<std::string_view> names;
  CollectTargets(lhs, names);
  if (!names.empty()) {
    const std::string& prefix = build.names.prefix;
    obj->run_key = (prefix.empty() ? "" : prefix + ".") + std::string(names[0]);
  }
  HangOn(obj, names, build.names);
  VpiHangOnVariablesNamed(obj, obj->lhs);
  names.clear();
  CollectReads(rhs, names);
  HangOn(obj, names, build.names);
}

const VpiObject* CalleeScope(const RtlirModule& mod,
                             const GenBlockPrefixes& prefixes,
                             VpiHandle instance) {
  for (auto it = prefixes.rbegin(); it != prefixes.rend(); ++it) {
    const std::string_view kBlock = *it;
    const auto kDeclared =
        std::ranges::find_if(mod.gen_block_subroutines,
                             [kBlock](const RtlirGenBlockSubroutine& sub) {
                               return !sub.gen_block_prefixes.empty() &&
                                      sub.gen_block_prefixes.back() == kBlock;
                             });
    if (kDeclared == mod.gen_block_subroutines.end()) continue;
    VpiHandle block = VpiGenScopeOf(instance, kDeclared->gen_block_path);
    return block != nullptr ? block : instance;
  }
  return instance;
}

}  // namespace

void VpiContext::AttachContinuousAssignments(const RtlirDesign* design,
                                             const VpiCallBuild& calls) {
  if (design == nullptr || design->top_modules.empty() ||
      design->top_modules.front() == nullptr) {
    return;
  }
  const std::string kFirstTop(design->top_modules.front()->name);
  const VpiAttachBuild kAttach{[this] { return AllocObject(); },
                               VpiPoolKeeper(name_pool_), sim_ctx_->GetArena()};
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiHandle scope = FindObjectForFlatName(
            object_map_, prefix.empty() ? kFirstTop : prefix);
        if (scope == nullptr) return;
        std::set<std::pair<const ModuleItem*, GenBlockPrefixes>> made;
        for (const RtlirContAssign& ca : mod->assigns) {
          if (ca.source_item == nullptr ||
              !made.emplace(ca.source_item, ca.gen_block_prefixes).second) {
            continue;
          }
          VpiObject* within = VpiGenScopeOf(scope, ca.gen_block_path);
          AssignBuild build{
              kAttach.alloc,
              sim_ctx_,
              AssignNames{object_map_, prefix, ca.gen_block_prefixes, within,
                          ca.gen_block_consts, scope, mod->imports,
                          mod->unit_index, calls.unit_typespecs},
              VpiCalleesAt({*design, *mod, prefix,
                            CalleeScope(*mod, ca.gen_block_prefixes, scope),
                            calls.subroutines}),
              kAttach.keep,
              VpiItemCallShaper(
                  {*design, *mod, prefix, ca.gen_block_prefixes, within},
                  object_map_, calls, kAttach),
              &mod->node_attrs};
          MakeContinuousAssignment(ca, within, build);
        }
      });
}

void AttachAliasStatements(const RtlirDesign* design,
                           const VpiObjectMap& objects, SimContext& ctx,
                           const VpiAttachBuild& build) {
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        for (const RtlirAlias& alias : mod->aliases) {
          const VpiExprNames kNames{objects, prefix, alias.gen_block_prefixes};
          for (std::size_t i = 0; i + 1 < alias.nets.size(); ++i) {
            VpiObject* stmt = build.alloc();
            stmt->type = vpiAliasStmt;
            stmt->parent = instance;
            stmt->lhs =
                VpiGenBlockExpression(alias.nets[i], kNames, ctx, build);
            stmt->rhs =
                VpiGenBlockExpression(alias.nets.back(), kNames, ctx, build);
            instance->children.push_back(stmt);
          }
        }
      });
}

}  // namespace delta
