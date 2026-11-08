#pragma once

#include <string_view>
#include <vector>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct Expr;
struct ModuleItem;
struct RtlirAssertionItemDecl;
struct RtlirDesign;
struct RtlirImport;
struct VpiObject;

struct VpiPropertyDeclSite {
  VpiObject* scope;
  const VpiObjectMap& unit_typespecs;
  SimContext& ctx;
  const std::vector<RtlirImport>& imports;
};

VpiObject* VpiMakePropertyDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with);

VpiObject* VpiMakeSequenceDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with);

void VpiFillAssertionItemDeclBody(VpiObject* made, const ModuleItem& decl,
                                  const VpiStmtBuild& with);

VpiObject* VpiFormalNames(VpiObject* made, const ModuleItem& decl,
                          SimContext& ctx, const VpiAttachBuild& build);

VpiObject* VpiMakeLetDecl(const ModuleItem& item, VpiObject* scope,
                          const VpiAttachBuild& build);

VpiObject* VpiLetFormalNames(VpiObject* made, const ModuleItem& item,
                             const VpiAttachBuild& build);

void VpiFillLetDecl(VpiObject* made, const ModuleItem& item,
                    const VpiStmtBuild& with);

void VpiAttachPackageAndUnitLets(const RtlirDesign& design,
                                 const VpiObjectMap& objects, SimContext& ctx,
                                 const VpiAttachBuild& build);

struct VpiAssertionDeclName {
  const VpiObject* scope;
  int type;
  std::string_view package;
  std::string_view name;
};

VpiObject* VpiAssertionDeclNamed(const VpiAssertionDeclName& named,
                                 const std::vector<RtlirImport>& imports,
                                 const VpiObjectMap& objects);

void AttachPackageAssertionItemDecls(const RtlirDesign& design,
                                     const VpiObjectMap& objects,
                                     const VpiObjectMap& unit_typespecs,
                                     SimContext& ctx,
                                     const VpiAttachBuild& build);

VpiObject* VpiMakePropertyInst(VpiObject* holder, const Expr& instance,
                               const Expr* disable, const VpiStmtBuild& with);

VpiObject* VpiPropertyOperandObject(const Expr& operand,
                                    const VpiStmtBuild& with);

VpiObject* VpiSequenceOperandObject(const Expr& operand,
                                    const VpiStmtBuild& with);

}  // namespace delta
