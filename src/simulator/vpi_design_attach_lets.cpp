#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_assertion_decls.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// Hangs `child` from `holder` where one was made.
void HangIfMade(VpiObject* holder, VpiObject* child) {
  if (child != nullptr) holder->children.push_back(child);
}

// What the let decls of a package or the compilation unit are built with:
// the design, whose operators' attributes it keeps, the objects its names
// resolve among, the run and the model's allocation.
struct LetScopeBuild {
  const RtlirDesign& design;
  const VpiObjectMap& objects;
  SimContext& ctx;
  const VpiAttachBuild& build;
};

// The let decls of the lets among `items`, under `scope`, a package or the
// compilation unit whose objects are keyed under `prefix`, each body's names
// found first among its formals' stand-ins and then in `scope`.
void AttachScopeLets(const std::vector<ModuleItem*>& items, VpiObject* scope,
                     const std::string& prefix, const LetScopeBuild& at) {
  const VpiAttachBuild& build = at.build;
  static const std::vector<std::string_view> kNoGenBlocks;
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kLetDecl) continue;
    VpiObject* made = VpiMakeLetDecl(*item, scope, build);
    const VpiExprNames kNames{at.objects,
                              prefix,
                              kNoGenBlocks,
                              VpiLetFormalNames(made, *item, build),
                              &at.design.node_attrs,
                              nullptr};
    const VpiStmtBuild kWith{build,
                             [&](const Expr* expr) {
                               return VpiGenBlockExpression(expr, kNames,
                                                            at.ctx, build);
                             },
                             nullptr,
                             nullptr,
                             nullptr,
                             nullptr};
    VpiFillLetDecl(made, *item, kWith);
  }
}

}  // namespace

VpiObject* VpiMakeLetDecl(const ModuleItem& item, VpiObject* scope,
                          const VpiAttachBuild& build) {
  VpiObject* made = build.alloc();
  made->type = vpiLetDecl;
  made->name = build.keep(std::string(item.name));
  made->full_name = VpiScopedFullName(scope, item.name);
  made->parent = scope;
  for (const FunctionArg& arg : item.func_args) {
    VpiObject* formal = build.alloc();
    formal->type = vpiSeqFormalDecl;
    formal->name = build.keep(std::string(arg.name));
    formal->parent = made;
    made->children.push_back(formal);
  }
  scope->children.push_back(made);
  return made;
}

VpiObject* VpiLetFormalNames(VpiObject* made, const ModuleItem& item,
                             const VpiAttachBuild& build) {
  VpiObject* names = build.alloc();
  names->parent = made;
  for (const FunctionArg& arg : item.func_args) {
    VpiObject* stand = build.alloc();
    stand->type = vpiRefObj;
    stand->parent = made;
    stand->name = build.keep(std::string(arg.name));
    names->children.push_back(stand);
  }
  return names;
}

void VpiFillLetDecl(VpiObject* made, const ModuleItem& item,
                    const VpiStmtBuild& with) {
  for (std::size_t i = 0; i < item.func_args.size(); ++i) {
    HangIfMade(made->children[i],
               with.expression(item.func_args[i].default_value));
  }
  HangIfMade(made, with.expression(item.init_expr));
}

void VpiAttachPackageAndUnitLets(const RtlirDesign& design,
                                 const VpiObjectMap& objects, SimContext& ctx,
                                 const VpiAttachBuild& build) {
  const LetScopeBuild kAt{design, objects, ctx, build};
  for (const PackageDecl* pkg : design.packages) {
    AttachScopeLets(pkg->items, FindObjectForFlatName(objects, pkg->name),
                    std::string(pkg->name), kAt);
  }
  VpiObject* unit = FindObjectForFlatName(objects, "$unit");
  if (unit != nullptr) AttachScopeLets(design.cu_let_decls, unit, "$unit", kAt);
}

}  // namespace delta
