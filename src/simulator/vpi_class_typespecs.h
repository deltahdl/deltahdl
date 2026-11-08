#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

namespace delta {

class SimContext;
struct ClassDecl;
struct DataType;
struct Expr;

void VpiAttachClassSpecializations(const VpiClassDefnObjects& defns,
                                   SimContext& ctx,
                                   const VpiAttachBuild& build);

VpiObject* VpiClassDefnOf(const VpiClassDefnObjects& defns,
                          const ClassDecl* decl, const std::string& scope,
                          const VpiObject* around);

const std::vector<VpiObject*>& VpiClassDefnList(int type,
                                                const VpiObject& defn);

VpiObject* VpiSpecializationTypespec(const VpiObject& defn,
                                     std::string_view name);

void VpiMakeExtendsParamAssigns(
    VpiObject* typespec, const ClassDecl& derived, const ClassDecl& base,
    const std::function<VpiObject*(const Expr*)>& expression,
    const VpiAttachBuild& build);

void VpiAssignExtendsNamedTypes(
    VpiObject* typespec, const ClassDecl& derived, const ClassDecl& base,
    const std::function<VpiObject*(const DataType&, VpiObject*)>& named);

int VpiClassTypeOf(const VpiObject& typespec);

VpiHandle VpiClassTypespecBase(const VpiObject& typespec);

}  // namespace delta
