#include <cstddef>
#include <string>

#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_design_attach_assertion_decls.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// Hangs `child` from `holder` where one was made.
void HangIfMade(VpiObject* holder, VpiObject* child) {
  if (child != nullptr) holder->children.push_back(child);
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

}  // namespace delta
