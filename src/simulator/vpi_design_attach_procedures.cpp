#include <algorithm>
#include <array>
#include <cstddef>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_assertion_decls.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_attach_procedures_internal.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_expr_decompile.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

int JoinTypeOf(TokenKind keyword) {
  if (keyword == TokenKind::kKwJoinAny) return vpiJoinAny;
  if (keyword == TokenKind::kKwJoinNone) return vpiJoinNone;
  return vpiJoin;
}

int BlockKind(const Stmt& stmt) {
  if (stmt.kind != StmtKind::kBlock && stmt.kind != StmtKind::kFork) return 0;
  bool is_fork = stmt.kind == StmtKind::kFork;
  if (!stmt.label.empty()) return is_fork ? vpiNamedFork : vpiNamedBegin;
  return is_fork ? vpiFork : vpiBegin;
}

VpiObject* MakeAtomicStatement(const Stmt& stmt, int type,
                               const BlockParent& parent,
                               const BodyWalk& walk) {
  VpiObject* obj = walk.build.alloc();
  obj->type = type;
  obj->parent = parent.scope;
  obj->process = walk.process;
  if (!stmt.label.empty()) obj->name = walk.build.keep(std::string(stmt.label));
  VpiRecordWrittenLocation(obj, stmt.range.start, walk.calls.ctx);
  walk.calls.stmts[{&stmt, walk.prefix}] = obj;
  parent.scope->children.push_back(obj);
  return obj;
}

int BlockVariableKind(const Stmt& decl, const BodyWalk& walk) {
  const int kKind = TypeVariableKind(decl.var_decl_type, walk);
  if (decl.var_unpacked_dims.empty()) return kKind;
  return kKind == vpiNamedEvent ? vpiNamedEventArray : vpiRegArray;
}

std::string BlockVariableRunKey(std::string_view name, const Stmt& stmt,
                                const BlockParent& parent,
                                const BodyWalk& walk) {
  std::string scopes = stmt.label.empty() ? "" : std::string(stmt.label) + ".";
  for (const BlockParent* outer = &parent; outer != nullptr;
       outer = outer->outer) {
    if (outer->block != nullptr && !outer->block->label.empty()) {
      scopes.insert(0, std::string(outer->block->label) + ".");
    }
  }
  if (scopes.empty()) return {};
  const std::string kGen =
      walk.gen_prefixes == nullptr || walk.gen_prefixes->empty()
          ? ""
          : std::string(walk.gen_prefixes->back());
  return VpiFlatName(walk.prefix, kGen + scopes + std::string(name));
}

bool InAutomaticSubroutine(const VpiObject* scope) {
  for (; scope != nullptr; scope = scope->parent) {
    if (VpiIsTaskFuncType(scope->type)) return scope->automatic;
  }
  return false;
}

void MakeBlockVariables(VpiObject* block, const Stmt& stmt,
                        const std::string& path, const BlockParent& parent,
                        const BodyWalk& walk) {
  for (const Stmt* item : BlockItems(stmt)) {
    if (item->kind != StmtKind::kVarDecl || item->var_is_param) continue;
    VpiObject* var = walk.build.alloc();
    var->type = BlockVariableKind(*item, walk);
    var->automatic = item->var_is_automatic ||
                     (!item->var_is_static && InAutomaticSubroutine(block));
    var->parent = block;
    var->name = walk.build.keep(std::string(item->var_name));
    var->full_name = path + "." + std::string(item->var_name);
    var->run_key = BlockVariableRunKey(item->var_name, stmt, parent, walk);
    block->children.push_back(var);
  }
}

std::string EventTriggerTargetName(const Stmt& stmt) {
  std::vector<std::string_view> names;
  if (!ChainNames(*stmt.expr, names)) return {};
  std::string joined(names.front());
  for (std::size_t i = 1; i < names.size(); ++i) {
    joined += "." + std::string(names[i]);
  }
  return joined;
}

VpiObject* TriggeredEvent(const std::string& name, const BlockParent& parent,
                          const BodyWalk& walk) {
  const BlockParent* where = nullptr;
  if (BlockVarDecl(parent, name, where) != nullptr) {
    return ChildNamed(where->scope, name);
  }
  std::string scope = walk.prefix;
  for (;;) {
    VpiObject* found =
        FindObjectForFlatName(walk.objects, VpiFlatName(scope, name));
    if (found != nullptr || scope.empty()) return found;
    const std::size_t kDot = scope.rfind('.');
    scope.resize(kDot == std::string::npos ? 0 : kDot);
  }
}

VpiObject* MakeEventStatement(const Stmt& stmt, const BlockParent& parent,
                              const BodyWalk& walk) {
  VpiObject* obj = MakeAtomicStatement(stmt, vpiEventStmt, parent, walk);
  obj->blocking = stmt.kind == StmtKind::kEventTrigger;
  const std::string kTarget = EventTriggerTargetName(stmt);
  if (kTarget.empty()) return obj;
  VpiObject* event = TriggeredEvent(kTarget, parent, walk);
  if (event != nullptr) obj->children.push_back(event);
  return obj;
}

void MakeCallArguments(VpiObject* call, const Expr& expr,
                       const BlockParent& parent, const BodyWalk& walk) {
  if (expr.kind != ExprKind::kCall && expr.kind != ExprKind::kSystemCall) {
    return;
  }
  const VpiCallSite kSite = CallSiteOf(parent, walk);
  for (const Expr* actual : expr.args) {
    VpiObject* arg = nullptr;
    if (actual == nullptr) {
      arg = walk.build.alloc();
      VpiMakeEmptyArgument(arg);
    } else if (actual->kind == ExprKind::kIdentifier &&
               actual->text == "null") {
      arg = walk.build.alloc();
      VpiMakeNullArgument(arg);
    } else {
      arg = VpiCallSiteExpression(actual, walk.objects, kSite, walk.calls.ctx,
                                  walk.build);
    }
    if (arg != nullptr) call->arguments.push_back(arg);
    call->written_arguments.push_back(arg);
  }
}

constexpr std::array<std::string_view, 10> kLocatorMethods = {
    "find",      "find_index",      "find_first", "find_first_index",
    "find_last", "find_last_index", "min",        "max",
    "unique",    "unique_index"};

VpiObject* InlineConstraint(const ClassMember& block, VpiObject* call,
                            const VpiObject* defn, const BlockParent& parent,
                            const BodyWalk& walk) {
  static const GenBlockPrefixes kNoGenBlocks;
  const VpiCallStand kStand{parent.scope, &walk.mod};
  VpiObject* constraint = VpiMakeConstraint(
      block, call,
      {walk.objects, walk.prefix,
       walk.gen_prefixes != nullptr ? *walk.gen_prefixes : kNoGenBlocks,
       VpiClassNameScope(defn, parent.scope, walk.build), walk.calls.ctx,
       nullptr, &kStand},
      walk.build);
  constraint->inline_constraint = true;
  return constraint;
}

void MakeWithClause(VpiObject* call, std::string_view method, const Expr& expr,
                    const BlockParent& parent, const BodyWalk& walk) {
  call->tf_with_method =
      call->type == vpiMethodFuncCall &&
      (method == "randomize" ||
       std::ranges::find(kLocatorMethods, method) != kLocatorMethods.end());
  if (!call->tf_with_method) return;
  if (expr.inline_constraint != nullptr) {
    call->tf_with = InlineConstraint(
        *expr.inline_constraint, call,
        MethodCallClassDefn(*expr.lhs, parent, walk), parent, walk);
  } else if (expr.with_expr != nullptr) {
    call->tf_with = VpiCallSiteExpression(expr.with_expr, walk.objects,
                                          CallSiteOf(parent, walk),
                                          walk.calls.ctx, walk.build);
  }
}

void FillCall(VpiObject* call, const CallShape& shape, const Expr& called,
              const BlockParent& parent, const BodyWalk& walk) {
  call->type = shape.type;
  if (!call->written_as_stmt) {
    call->name = walk.build.keep(std::string(shape.name));
  }
  call->tf_prefix = shape.prefix;
  call->prefix_members = shape.prefix_members;
  call->tf_decl = shape.called;
  call->func_type =
      shape.called != nullptr ? shape.called->func_type : shape.sysfunctype;
  call->user_defined = shape.user_defined;
  call->user_systf = shape.systf;
  MakeCallArguments(call, called, parent, walk);
  MakeWithClause(call, shape.name, called, parent, walk);
  walk.calls.sites[{&called, walk.prefix}] = call;
}

VpiObject* MakeCallStatement(const Stmt& stmt, const BlockParent& parent,
                             const BodyWalk& walk) {
  if (stmt.kind != StmtKind::kExprStmt) return nullptr;
  const Expr* called =
      stmt.expr->kind == ExprKind::kCast ? stmt.expr->lhs : stmt.expr;
  const CallShape kShape = CallShapeOf(*called, parent, walk);
  if (kShape.type == 0) return nullptr;
  VpiObject* call = MakeAtomicStatement(stmt, kShape.type, parent, walk);
  call->written_as_stmt = true;
  FillCall(call, kShape, *called, parent, walk);
  if (kShape.type == vpiSysTaskCall || kShape.type == vpiSysFuncCall) {
    call->decompile = VpiExprDecompile(called);
  }
  return call;
}

bool LabelCreatesNamedBegin(const Stmt& stmt) {
  if (stmt.label.empty() || stmt.kind == StmtKind::kBlock ||
      stmt.kind == StmtKind::kFork || stmt.kind == StmtKind::kForeach) {
    return false;
  }
  return stmt.kind != StmtKind::kFor || stmt.for_init_types.empty() ||
         stmt.for_init_types.front().kind == DataTypeKind::kImplicit;
}

VpiObject* MakeScopeObject(int kind, std::string_view label,
                           const BlockParent& parent, const BodyWalk& walk,
                           std::string& path) {
  VpiObject* scope = walk.build.alloc();
  scope->type = kind;
  scope->parent = parent.scope;
  scope->process = walk.process;
  path = parent.path;
  if (!label.empty()) {
    scope->name = walk.build.keep(std::string(label));
    path += "." + std::string(label);
    scope->full_name = path;
  }
  parent.scope->children.push_back(scope);
  return scope;
}

VpiObject* WalkStmt(const Stmt* stmt, const BlockParent& parent,
                    const BodyWalk& walk);

void WalkSubStmts(const Stmt& stmt, const BlockParent& parent,
                  const BodyWalk& walk) {
  ForEachChildStmt(&stmt,
                   [&](const Stmt* sub) { WalkStmt(sub, parent, walk); });
}

VpiStmtBuild StmtBuildAt(const BlockParent& parent, const BodyWalk& walk) {
  return {walk.build,
          [site = CallSiteOf(parent, walk), &walk](const Expr* expr) {
            return VpiCallSiteExpression(expr, walk.objects, site,
                                         walk.calls.ctx, walk.build);
          },
          [&parent, &walk](const Stmt* held, VpiObject* holder) {
            return WalkStmt(
                held, BlockParent{holder, parent.path, nullptr, &parent}, walk);
          },
          [&parent, &walk](const Expr* array) {
            return ForeachIndexKind(array, parent, walk);
          },
          [site = CallSiteOf(parent, walk), &walk](const Expr* expr,
                                                   const VpiObject* target) {
            return VpiCallSiteAssignedExpression(
                {expr, target}, walk.objects, site, walk.calls.ctx, walk.build);
          },
          [&parent, &walk](int type, std::string_view package,
                           std::string_view name) {
            return VpiAssertionDeclNamed({parent.scope, type, package, name},
                                         walk.mod.imports, walk.objects);
          }};
}

VpiObject* MakeBuiltStmt(const Stmt& stmt, const BlockParent& parent,
                         const BodyWalk& walk) {
  const int kKind = VpiBuiltStmtKind(stmt);
  if (kKind == 0) return nullptr;
  VpiObject* obj = MakeAtomicStatement(stmt, kKind, parent, walk);
  if (VpiIsAssertionType(kKind)) {
    VpiRecordAssertionLocation(obj, stmt.range, walk.calls.ctx);
    const bool kInOwnLabel = parent.block == nullptr &&
                             parent.scope->type == vpiNamedBegin &&
                             parent.scope->name == stmt.label;
    if (!stmt.label.empty()) {
      obj->full_name = kInOwnLabel
                           ? parent.path
                           : parent.path + "." + std::string(stmt.label);
    }
  }
  VpiFillStmt(obj, stmt, StmtBuildAt(parent, walk));
  return obj;
}

VpiObject* MakeBlock(const Stmt& stmt, int kind, const BlockParent& parent,
                     const BodyWalk& walk) {
  std::string path;
  VpiObject* block = MakeScopeObject(kind, stmt.label, parent, walk, path);
  VpiRecordWrittenLocation(block, stmt.range.start, walk.calls.ctx);
  walk.calls.stmts[{&stmt, walk.prefix}] = block;
  if (stmt.kind == StmtKind::kFork) {
    block->join_type = JoinTypeOf(stmt.join_kind);
  }
  MakeBlockVariables(block, stmt, path, parent, walk);
  WalkSubStmts(stmt, BlockParent{block, path, &stmt, &parent}, walk);
  return block;
}

VpiObject* MakeIncDecStatement(const Stmt& stmt, const BlockParent& parent,
                               const BodyWalk& walk) {
  if (stmt.kind != StmtKind::kExprStmt || stmt.expr == nullptr) return nullptr;
  const int kOperator = VpiIncDecOpType(
      stmt.expr->op, stmt.expr->kind == ExprKind::kPostfixUnary);
  if (kOperator == 0) return nullptr;
  VpiObject* obj = MakeAtomicStatement(stmt, vpiAssignment, parent, walk);
  obj->op_type = kOperator;
  obj->blocking = true;
  obj->lhs = StmtBuildAt(parent, walk).expression(stmt.expr->lhs);
  return obj;
}

VpiObject* WalkStmtItself(const Stmt& stmt, const BlockParent& parent,
                          const BodyWalk& walk) {
  if (VpiObject* step = MakeIncDecStatement(stmt, parent, walk)) return step;
  if (stmt.kind == StmtKind::kEventTrigger ||
      stmt.kind == StmtKind::kNbEventTrigger) {
    return MakeEventStatement(stmt, parent, walk);
  }
  const int kAtomic = VpiBareAtomicKind(stmt.kind);
  if (kAtomic != 0) return MakeAtomicStatement(stmt, kAtomic, parent, walk);
  VpiObject* call = MakeCallStatement(stmt, parent, walk);
  if (call != nullptr) return call;
  VpiObject* made = MakeBuiltStmt(stmt, parent, walk);
  if (made != nullptr) return made;
  const int kBlock = BlockKind(stmt);
  if (kBlock != 0) return MakeBlock(stmt, kBlock, parent, walk);
  WalkSubStmts(stmt, parent, walk);
  return nullptr;
}

VpiObject* WithStmtAttributes(VpiObject* obj, const Stmt& stmt,
                              const BodyWalk& walk) {
  if (obj != nullptr) {
    VpiAttachAttributes(obj, VpiNodeAttributes(&walk.mod, &stmt), false,
                        walk.calls.ctx, walk.build);
  }
  return obj;
}

VpiObject* WalkStmt(const Stmt* stmt, const BlockParent& parent,
                    const BodyWalk& walk) {
  if (stmt == nullptr) return nullptr;
  if (!LabelCreatesNamedBegin(*stmt)) {
    return WithStmtAttributes(WalkStmtItself(*stmt, parent, walk), *stmt, walk);
  }
  std::string path;
  VpiObject* begin =
      MakeScopeObject(vpiNamedBegin, stmt->label, parent, walk, path);
  WithStmtAttributes(
      WalkStmtItself(*stmt, BlockParent{begin, path, nullptr, &parent}, walk),
      *stmt, walk);
  return begin;
}

VpiObject* WalkProcessBody(const RtlirProcess& proc, const BlockParent& parent,
                           const BodyWalk& walk) {
  const bool kAlways = proc.kind == RtlirProcessKind::kAlways ||
                       proc.kind == RtlirProcessKind::kAlwaysFF;
  if (!kAlways || (proc.sensitivity.empty() && !proc.is_star_sensitivity)) {
    return WalkStmt(proc.body, parent, walk);
  }
  Stmt control{};
  control.kind = StmtKind::kEventControl;
  control.events = proc.sensitivity;
  control.is_star_event = proc.is_star_sensitivity;
  control.body = proc.body;
  return MakeBuiltStmt(control, parent, walk);
}

int AlwaysTypeOf(RtlirProcessKind kind) {
  if (kind == RtlirProcessKind::kInitial || kind == RtlirProcessKind::kFinal) {
    return 0;
  }
  if (kind == RtlirProcessKind::kAlwaysComb) return vpiAlwaysComb;
  if (kind == RtlirProcessKind::kAlwaysFF) return vpiAlwaysFF;
  return kind == RtlirProcessKind::kAlwaysLatch ? vpiAlwaysLatch : vpiAlways;
}

VpiObject* MakeProcess(const RtlirProcess& proc, VpiObject* scope,
                       const VpiAttachBuild& build) {
  VpiObject* process = build.alloc();
  process->always_type = AlwaysTypeOf(proc.kind);
  process->type = vpiAlways;
  if (proc.kind == RtlirProcessKind::kInitial) process->type = vpiInitial;
  if (proc.kind == RtlirProcessKind::kFinal) process->type = vpiFinal;
  process->parent = scope;
  scope->children.push_back(process);
  return process;
}

template <typename Scoped, typename Make>
void AttachScopedItems(VpiObject* instance, const BodyWalk& instance_walk,
                       const std::vector<Scoped>& items, const Make& make) {
  for (const Scoped& entry : items) {
    VpiObject* scope = VpiGenScopeOf(instance, entry.gen_block_path);
    BodyWalk walk = instance_walk;
    walk.gen_prefixes = &entry.gen_block_prefixes;
    const BlockParent kParent{scope, scope->full_name};
    make(entry, scope, StmtBuildAt(kParent, walk));
  }
}

using DeclMaker = VpiObject* (*)(const RtlirAssertionItemDecl&,
                                 const VpiPropertyDeclSite&,
                                 const VpiStmtBuild&);

VpiObject* MakeAttributedDecl(DeclMaker make,
                              const RtlirAssertionItemDecl& declared,
                              VpiObject* scope, const VpiStmtBuild& with,
                              const BodyWalk& instance_walk) {
  const VpiCallBuild& calls = instance_walk.calls;
  VpiObject* made =
      make(declared,
           {scope, calls.unit_typespecs, calls.ctx, instance_walk.mod.imports},
           with);
  VpiAttachAttributes(made,
                      VpiNodeAttributes(&instance_walk.mod, declared.item),
                      false, calls.ctx, instance_walk.build);
  return made;
}

bool IsSequenceDecl(const RtlirAssertionItemDecl& declared) {
  return declared.item->kind == ModuleItemKind::kSequenceDecl;
}

void AttachLetDecl(const ModuleItem& item, VpiObject* scope,
                   const BodyWalk& walk) {
  VpiObject* made = VpiMakeLetDecl(item, scope, walk.build);
  const BlockParent kParent{scope, scope->full_name, nullptr, nullptr,
                            VpiLetFormalNames(made, item, walk.build)};
  VpiFillLetDecl(made, item, StmtBuildAt(kParent, walk));
}

void AttachInstanceLetDecls(VpiObject* instance, const BodyWalk& walk) {
  std::unordered_set<const ModuleItem*> in_blocks;
  for (const RtlirGenBlockLet& let : walk.mod.gen_block_lets) {
    in_blocks.insert(let.item);
    BodyWalk in_block = walk;
    in_block.gen_prefixes = &let.gen_block_prefixes;
    AttachLetDecl(*let.item, VpiGenScopeOf(instance, let.gen_block_path),
                  in_block);
  }
  for (const ModuleItem* item : walk.mod.let_decls) {
    if (item->kind != ModuleItemKind::kLetDecl || in_blocks.contains(item)) {
      continue;
    }
    AttachLetDecl(*item, instance, walk);
  }
}

void AttachInstanceAssertionItemDecls(VpiObject* instance,
                                      const BodyWalk& instance_walk) {
  const auto& declared = instance_walk.mod.assertion_item_decls;
  std::vector<VpiObject*> made;
  AttachScopedItems(
      instance, instance_walk, declared,
      [&instance_walk, &made](const RtlirAssertionItemDecl& item,
                              VpiObject* scope, const VpiStmtBuild& with) {
        made.push_back(MakeAttributedDecl(
            IsSequenceDecl(item) ? VpiMakeSequenceDecl : VpiMakePropertyDecl,
            item, scope, with, instance_walk));
      });
  for (size_t i = 0; i < declared.size(); ++i) {
    VpiObject* scope = VpiGenScopeOf(instance, declared[i].gen_block_path);
    BodyWalk walk = instance_walk;
    walk.gen_prefixes = &declared[i].gen_block_prefixes;
    const BlockParent kParent{
        scope, scope->full_name, nullptr, nullptr,
        VpiFormalNames(made[i], *declared[i].item, instance_walk.calls.ctx,
                       instance_walk.build)};
    VpiFillAssertionItemDeclBody(made[i], *declared[i].item,
                                 StmtBuildAt(kParent, walk));
  }
}

void AttachInstanceProcedures(VpiObject* instance,
                              const BodyWalk& instance_walk) {
  AttachScopedItems(
      instance, instance_walk, instance_walk.mod.assertions,
      [&instance_walk](const RtlirAssertion& assertion, VpiObject* scope,
                       const VpiStmtBuild& with) {
        VpiObject* made = VpiMakeItemAssertion(assertion, scope,
                                               instance_walk.calls.ctx, with);
        if (made != nullptr) {
          VpiAttachAttributes(
              made, VpiNodeAttributes(&instance_walk.mod, assertion.item),
              false, instance_walk.calls.ctx, instance_walk.build);
        }
      });
  for (const RtlirProcess& proc : instance_walk.mod.processes) {
    VpiObject* scope = VpiGenScopeOf(instance, proc.gen_block_path);
    BodyWalk walk = instance_walk;
    walk.gen_prefixes = &proc.gen_block_prefixes;
    const BlockParent kParent{scope, scope->full_name};
    if (!proc.is_static_assertion) {
      walk.process = MakeProcess(proc, scope, instance_walk.build);
      VpiRecordWrittenLocation(walk.process, proc.loc, instance_walk.calls.ctx);
      VpiAttachAttributes(walk.process, proc.attrs, false,
                          instance_walk.calls.ctx, instance_walk.build);
      walk.process->body = WalkProcessBody(proc, kParent, walk);
    } else if (proc.body->is_deferred) {
      MakeBuiltStmt(*proc.body, kParent, walk);
    }
  }
}

void WalkSubroutineBody(const ModuleItem& item, VpiObject* tf,
                        const BodyWalk& walk) {
  std::vector<Stmt*> statements;
  for (Stmt* stmt : item.func_body_stmts) {
    if (stmt->kind != StmtKind::kVarDecl) statements.push_back(stmt);
  }
  if (statements.empty()) return;
  const BlockParent kParent{tf, tf->full_name};
  if (statements.size() == 1) {
    WalkStmt(statements.front(), kParent, walk);
    return;
  }
  Stmt* begin = walk.build.arena.Create<Stmt>();
  begin->kind = StmtKind::kBlock;
  begin->range = statements.front()->range;
  begin->stmts = std::move(statements);
  MakeBlock(*begin, vpiBegin, kParent, walk);
}

void AttachInstanceSubroutineBodies(VpiObject* instance, const BodyWalk& walk) {
  for (const auto& [key, tf] : walk.calls.subroutines) {
    if (key.second == walk.prefix) WalkSubroutineBody(*key.first, tf, walk);
  }
  for (const RtlirGenBlockSubroutine& sub : walk.mod.gen_block_subroutines) {
    const VpiObject* block = VpiGenScopeOf(instance, sub.gen_block_path);
    BodyWalk in_block = walk;
    in_block.gen_prefixes = &sub.gen_block_prefixes;
    WalkSubroutineBody(*sub.decl,
                       walk.calls.subroutines.at({sub.decl, block->full_name}),
                       in_block);
  }
}

void AttachPackageSubroutineBodies(const RtlirDesign& design,
                                   const VpiObjectMap& objects,
                                   const VpiCallBuild& calls,
                                   const VpiAttachBuild& build) {
  static const RtlirModule kNoModule{};
  for (const PackageDecl* pkg : design.packages) {
    const std::string kPackage(pkg->name);
    BodyWalk walk{design, kNoModule, objects, kPackage, calls, build};
    walk.package = pkg->name;
    for (const ModuleItem* item : pkg->items) {
      const auto kMade = calls.subroutines.find({item, kPackage});
      if (kMade != calls.subroutines.end()) {
        WalkSubroutineBody(*item, kMade->second, walk);
      }
    }
  }
  const std::string kUnit("$unit");
  for (const VpiUnitScope& at : VpiUnitScopes(design, objects)) {
    auto* in_unit = build.arena.Create<RtlirModule>();
    in_unit->unit_index = at.index;
    const BodyWalk kUnitWalk{design, *in_unit, objects, kUnit, calls, build};
    for (const ModuleItem* item : at.unit->cu_items) {
      if (item->kind == ModuleItemKind::kDpiImport) continue;
      const auto kMade = calls.subroutines.find({item, kUnit});
      if (kMade != calls.subroutines.end()) {
        WalkSubroutineBody(*item, kMade->second, kUnitWalk);
      }
    }
  }
}

VpiObject* MethodObject(const VpiObject& defn, const ModuleItem& method) {
  return *std::ranges::find_if(
      defn.children, [&method](const VpiObject* child) {
        return VpiIsTaskFuncType(child->type) && child->name == method.name;
      });
}

void AttachClassMethodBodies(const RtlirDesign& design,
                             const VpiObjectMap& objects,
                             const VpiCallBuild& calls,
                             const VpiAttachBuild& build) {
  static const RtlirModule kNoModule{};
  std::unordered_map<std::string, const RtlirModule*> modules;
  WalkInstancePaths(&design,
                    [&](const RtlirModule* mod, const std::string& prefix) {
                      modules.emplace(prefix, mod);
                    });
  for (const auto& [key, defn] : calls.classes) {
    const auto kModule = modules.find(key.second);
    const bool kInModule = kModule != modules.end();
    BodyWalk walk{design,  kInModule ? *kModule->second : kNoModule,
                  objects, key.second,
                  calls,   build};
    if (!kInModule) walk.package = key.second;
    for (const ClassMember* member : key.first->members) {
      if (member->method == nullptr) continue;
      const ModuleItem* body = member->method->out_of_block_body != nullptr
                                   ? member->method->out_of_block_body
                                   : member->method;
      WalkSubroutineBody(*body, MethodObject(*defn, *member->method), walk);
    }
  }
}

}  // namespace

bool ShapeExprCall(const Expr& call, VpiObject* made, const BlockParent& parent,
                   const BodyWalk& walk) {
  CallShape shape = CallShapeOf(call, parent, walk);
  if (shape.type == 0) return false;
  if (call.kind == ExprKind::kSystemCall) shape.type = vpiSysFuncCall;
  made->parent = parent.scope;
  FillCall(made, shape, call, parent, walk);
  return true;
}

std::function<bool(const Expr& call, VpiObject* made)> VpiItemCallShaper(
    const VpiItemSite& site, const VpiObjectMap& objects,
    const VpiCallBuild& calls, const VpiAttachBuild& build) {
  return [site, &objects, &calls, &build](const Expr& call, VpiObject* made) {
    BodyWalk walk{site.design, site.mod, objects, site.prefix, calls, build};
    walk.gen_prefixes = &site.gen_prefixes;
    const BlockParent kParent{site.scope, site.scope->full_name};
    return ShapeExprCall(call, made, kParent, walk);
  };
}

const Stmt* BlockVarDecl(const BlockParent& parent, std::string_view name,
                         const BlockParent*& where) {
  for (const BlockParent* at = &parent; at != nullptr; at = at->outer) {
    if (at->block == nullptr) continue;
    for (const Stmt* item : BlockItems(*at->block)) {
      if (item->kind == StmtKind::kVarDecl && item->var_name == name) {
        where = at;
        return item;
      }
    }
  }
  return nullptr;
}

bool ChainNames(const Expr& expr, std::vector<std::string_view>& names) {
  if (expr.kind == ExprKind::kIdentifier) {
    names.push_back(expr.text);
    return true;
  }
  if (expr.kind != ExprKind::kMemberAccess || expr.is_scope_resolution) {
    return false;
  }
  if (!ChainNames(*expr.lhs, names)) return false;
  names.push_back(expr.rhs->text);
  return true;
}

void VpiShapeDeferredCalls(const RtlirDesign* design,
                           const VpiObjectMap& objects,
                           std::vector<VpiDeferredCall>& deferred,
                           const VpiCallBuild& calls,
                           const VpiAttachBuild& build) {
  static const RtlirModule kNoModule{};
  for (std::size_t index = 0; index < deferred.size(); ++index) {
    VpiDeferredCall held = std::move(deferred[index]);
    BodyWalk walk{
        *design, held.stand.mod != nullptr ? *held.stand.mod : kNoModule,
        objects, held.prefix,
        calls,   build};
    walk.gen_prefixes = &held.gen_prefixes;
    walk.package = held.stand.package;
    const BlockParent kParent{held.stand.scope, held.stand.scope->full_name};
    if (!ShapeExprCall(*held.call, held.made, kParent, walk)) {
      MakeCallArguments(held.made, *held.call, kParent, walk);
    }
  }
}

void AttachProcedures(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiCallBuild& calls, const VpiAttachBuild& build) {
  if (design->top_modules.empty() || design->top_modules.front() == nullptr) {
    return;
  }
  const std::string kFirstTop(design->top_modules.front()->name);
  const auto kWalk = [&](void (*attach)(VpiObject*, const BodyWalk&)) {
    WalkInstancePaths(
        design, [&](const RtlirModule* mod, const std::string& prefix) {
          attach(FindObjectForFlatName(objects,
                                       prefix.empty() ? kFirstTop : prefix),
                 BodyWalk{*design, *mod, objects, prefix, calls, build});
        });
  };
  kWalk(AttachInstanceLetDecls);
  kWalk(AttachInstanceAssertionItemDecls);
  kWalk(AttachInstanceProcedures);
  kWalk(AttachInstanceSubroutineBodies);
  AttachPackageSubroutineBodies(*design, objects, calls, build);
  AttachClassMethodBodies(*design, objects, calls, build);
  VpiResolveDisableTargets(calls.stmts);
}

}  // namespace delta
