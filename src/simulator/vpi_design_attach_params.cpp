#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/packed_range.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_defparam.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"
#include "parser/ast_type.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_model_helpers3.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

struct ParamAttach {
  const VpiObjectMap& unit;
  const VpiAttachBuild& build;
  SimContext& ctx;
};

struct ParamScope {
  VpiObject* scope;
  const std::string& prefix;
  const VpiObjectMap& objects;
  const ModuleDecl& decl;
  const RtlirModule& mod;
};

struct ParamArrayAttach {
  const VpiObjectMap& objects;
  SimContext& ctx;
  const VpiAttachBuild& build;
  const RtlirModule* mod = nullptr;
  const VpiObject* instance = nullptr;
};

VpiObject* TypespecNamed(const VpiObject& scope, std::string_view name) {
  for (VpiObject* child : scope.children) {
    if (child != nullptr && child->type != vpiTypeParameter &&
        VpiIsTypespecType(child->type) && child->name == name) {
      return child;
    }
  }
  return nullptr;
}

VpiObject* TypeParameterTypespec(const DataType& type, VpiObject* scope,
                                 const VpiObjectMap& unit,
                                 const VpiAttachBuild& build) {
  if (type.kind == DataTypeKind::kNamed) {
    for (const VpiObject* at = scope; at != nullptr; at = at->parent) {
      if (VpiObject* found = TypespecNamed(*at, type.type_name)) return found;
    }
    auto in_unit = unit.find(type.type_name);
    return in_unit == unit.end() ? nullptr : in_unit->second;
  }
  const int kKind = VpiTypespecKind(type.kind);
  if (kKind == 0) return nullptr;
  VpiObject* typespec = build.alloc();
  typespec->type = kKind;
  return typespec;
}

void MakeTypeParameter(VpiObject* scope, const RtlirParamDecl& param,
                       const DataType* default_type, const ParamAttach& with) {
  const VpiAttachBuild& build = with.build;
  VpiObject* obj = build.alloc();
  obj->type = vpiTypeParameter;
  obj->name = build.keep(std::string(param.name));
  obj->full_name = VpiScopedFullName(scope, param.name);
  obj->parent = scope;
  obj->local_param = param.is_localparam;
  if (param.resolved_type != nullptr) {
    obj->param_typespec =
        TypeParameterTypespec(*param.resolved_type, scope, with.unit, build);
  }
  if (default_type != nullptr) {
    obj->param_default =
        TypeParameterTypespec(*default_type, scope, with.unit, build);
  }
  VpiRecordWrittenLocation(obj, param.loc, with.ctx);
  scope->children.push_back(obj);
}

const DataType* DeclaredDefaultType(const ModuleDecl& decl,
                                    std::string_view name) {
  for (std::size_t i = 0; i < decl.params.size(); ++i) {
    if (decl.params[i].first != name || i >= decl.param_types.size()) continue;
    const DataType& type = decl.param_types[i];
    return type.kind == DataTypeKind::kImplicit ? nullptr : &type;
  }
  const auto kItem =
      std::ranges::find_if(decl.items, [name](const ModuleItem* item) {
        return item->kind == ModuleItemKind::kParamDecl && item->name == name;
      });
  return kItem == decl.items.end() ? nullptr : &(*kItem)->typedef_type;
}

int ParameterConstType(const RtlirParamDecl& param) {
  if (param.decl_is_real || param.is_real_value) return vpiRealConst;
  return param.is_string_value ? vpiStringConst : vpiIntConst;
}

VpiObject* ParameterTypespec(const RtlirParamDecl& param, const VpiObject& obj,
                             VpiObject* scope, const ParamAttach& with) {
  const bool kWritten = param.decl_type != nullptr && !param.decl_type_implicit;
  DataType inferred;
  inferred.kind = ParameterConstType(param) == vpiRealConst
                      ? DataTypeKind::kReal
                  : param.is_string_value ? DataTypeKind::kString
                                          : DataTypeKind::kLogic;
  VpiObject* typespec = TypeParameterTypespec(
      kWritten ? *param.decl_type : inferred, scope, with.unit, with.build);
  if (typespec == nullptr || typespec->type != vpiLogicTypespec ||
      (kWritten && param.decl_type->kind == DataTypeKind::kNamed)) {
    return typespec;
  }
  const int64_t kWidth = obj.var != nullptr ? obj.var->value.width : 1;
  if (param.has_decl_range_bounds) {
    typespec->children.push_back(VpiRangeObject(
        typespec, PackedRange{param.decl_range_left, param.decl_range_right},
        with.build));
  } else if (!kWritten && kWidth > 1) {
    typespec->children.push_back(
        VpiRangeObject(typespec, PackedRange{kWidth - 1, 0}, with.build));
  }
  return typespec;
}

void DescribeValueParameter(VpiObject& obj, const RtlirParamDecl& param,
                            const ParamScope& at, const ParamAttach& with) {
  obj.const_type = ParameterConstType(param);
  if (param.has_decl_range_bounds) {
    obj.explicit_param_range = true;
    obj.param_left_range = VpiIntConstant(param.decl_range_left, with.build);
    obj.param_right_range = VpiIntConstant(param.decl_range_right, with.build);
  }
  if (param.default_value != nullptr) {
    static const GenBlockPrefixes kNoGenBlocks;
    obj.param_default =
        VpiGenBlockExpression(param.default_value,
                              {at.objects, at.prefix, kNoGenBlocks, nullptr,
                               nullptr, nullptr, &at.mod, at.scope},
                              with.ctx, with.build);
  }
  if (VpiObject* typespec = ParameterTypespec(param, obj, at.scope, with)) {
    obj.children.push_back(typespec);
  }
}

VpiObject* ParameterScope(const RtlirModule& mod, std::size_t index,
                          VpiObject* scope) {
  if (scope == nullptr || mod.params[index].gen_block_prefix.empty()) {
    return scope;
  }
  const auto kMember = std::ranges::find_if(
      mod.gen_block_members, [index](const RtlirGenBlockMember& member) {
        return member.kind == RtlirGenBlockMember::Kind::kParam &&
               member.param_index == index;
      });
  if (kMember == mod.gen_block_members.end()) return nullptr;
  return VpiGenScopeOf(scope, kMember->gen_block_path);
}

void AttachScopeParameters(const RtlirModule* mod, const ParamScope& at,
                           const ParamAttach& with) {
  for (std::size_t i = 0; i < mod->params.size(); ++i) {
    const RtlirParamDecl& param = mod->params[i];
    if (param.is_type_param) {
      if (VpiObject* holder = ParameterScope(*mod, i, at.scope)) {
        MakeTypeParameter(holder, param,
                          param.gen_block_prefix.empty()
                              ? DeclaredDefaultType(at.decl, param.name)
                              : nullptr,
                          with);
      }
      continue;
    }
    VpiObject* obj = FindObjectForFlatName(
        at.objects, VpiFlatName(at.prefix, std::string(param.gen_block_prefix) +
                                               std::string(param.name)));
    if (obj == nullptr) continue;
    obj->type = vpiParameter;
    obj->local_param = param.is_localparam;
    VpiRecordWrittenLocation(obj, param.loc, with.ctx);
    DescribeValueParameter(*obj, param, at, with);
  }
}

void AttachScopeSpecParams(const RtlirModule* mod, const std::string& prefix,
                           const VpiObjectMap& objects) {
  std::vector<std::string_view> names = mod->specparam_names;
  for (const ModuleItem* block : mod->specify_blocks) {
    for (const SpecifyItem* item : block->specify_items) {
      if (item->kind == SpecifyItemKind::kSpecparam) {
        names.push_back(item->param_name);
      }
    }
  }
  for (std::string_view name : names) {
    VpiObject* obj =
        FindObjectForFlatName(objects, VpiFlatName(prefix, std::string(name)));
    if (obj != nullptr) obj->type = vpiSpecParam;
  }
}

void AttachPackageParameters(const PackageDecl& pkg, VpiObject& scope,
                             const ParamAttach& with) {
  for (const ModuleItem* item : pkg.items) {
    if (item == nullptr || item->kind != ModuleItemKind::kParamDecl) continue;
    if (item->data_type.kind == DataTypeKind::kVoid) {
      RtlirParamDecl param;
      param.name = item->name;
      param.loc = item->loc;
      param.is_localparam = true;
      param.is_type_param = true;
      param.resolved_type = &item->typedef_type;
      MakeTypeParameter(&scope, param, &item->typedef_type, with);
      continue;
    }
    for (VpiObject* child : scope.children) {
      if (child->name == item->name && !VpiIsTypespecType(child->type)) {
        child->type = vpiParameter;
        child->local_param = true;
        VpiRecordWrittenLocation(child, item->loc, with.ctx);
      }
    }
  }
}

void AttachDefParams(const RtlirDesign* design, const VpiObjectMap& objects,
                     SimContext& ctx, const VpiAttachBuild& build) {
  std::unordered_map<const RtlirModule*, std::string> prefixes;
  WalkInstancePaths(design,
                    [&](const RtlirModule* mod, const std::string& prefix) {
                      prefixes.try_emplace(mod, prefix);
                    });
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        for (const RtlirDefparam& defparam : mod->defparams) {
          VpiObject* made = build.alloc();
          made->type = vpiDefParam;
          made->parent = instance;
          made->lhs = FindObjectForFlatName(
              objects, VpiFlatName(prefixes[defparam.target_module],
                                   defparam.target_name));
          made->rhs =
              VpiInstanceExpression(defparam.rhs, objects, prefix, ctx, build);
          instance->children.push_back(made);
        }
      });
}

VpiObject* InstanceParameter(const std::string& instance, std::string_view name,
                             const VpiObjectMap& objects) {
  VpiObject* scope = FindObjectForFlatName(objects, instance);
  if (scope == nullptr) return nullptr;
  const auto kFound =
      std::ranges::find_if(scope->children, [name](const VpiObject* child) {
        const bool kParameter =
            child->type == vpiParameter || child->type == vpiTypeParameter;
        return kParameter && child->name == name;
      });
  return kFound == scope->children.end() ? nullptr : *kFound;
}

void MakeArrayParamAssigns(VpiObject* array, const RtlirModuleInst& left,
                           const ModuleItem& item, const std::string& prefix,
                           const ParamArrayAttach& with) {
  const std::vector<std::string_view> kOrdered =
      OverridableParamNames(&VpiDeclOf(*left.resolved));
  for (std::size_t k = 0; k < item.inst_params.size(); ++k) {
    const auto& [name, value] = item.inst_params[k];
    if (value == nullptr) continue;
    VpiObject* made = with.build.alloc();
    made->type = vpiParamAssign;
    made->parent = array;
    made->conn_by_name = !name.empty();
    if (VpiObject* lhs = InstanceParameter(VpiFlatName(prefix, left.inst_name),
                                           name.empty() ? kOrdered[k] : name,
                                           with.objects)) {
      made->children.push_back(lhs);
    }
    static const GenBlockPrefixes kNoGenBlocks;
    made->rhs =
        VpiGenBlockExpression(value,
                              {with.objects, prefix, kNoGenBlocks, nullptr,
                               nullptr, nullptr, with.mod, with.instance},
                              with.ctx, with.build);
    array->children.push_back(made);
  }
}

struct ParamAssignHolder {
  VpiObject* holder;
  std::string_view written;
};

ParamAssignHolder HolderOf(const RtlirModuleInst& left,
                           const std::string& prefix,
                           const VpiObjectMap& objects) {
  VpiObject* instance =
      FindObjectForFlatName(objects, VpiFlatName(prefix, left.inst_name));
  if (left.array.name.empty()) return {instance, left.inst_name};
  return {VpiInstanceArrayOf(instance, vpiInstanceArray), left.array.name};
}

void MakeInstanceArrayParamAssigns(const RtlirModule& mod,
                                   const std::string& prefix,
                                   const ParamArrayAttach& with) {
  const ModuleDecl& decl = VpiDeclOf(mod);
  for (const RtlirModuleInst& left : mod.children) {
    if (!left.array.name.empty() && left.array.index != left.array.left) {
      continue;
    }
    const ParamAssignHolder kAt = HolderOf(left, prefix, with.objects);
    if (kAt.holder == nullptr) continue;
    for (const ModuleItem* item : decl.items) {
      if (item->kind == ModuleItemKind::kModuleInst &&
          item->inst_name == kAt.written) {
        MakeArrayParamAssigns(kAt.holder, left, *item, prefix, with);
      }
    }
  }
}

}  // namespace

void AttachParameters(const RtlirDesign* design, const VpiObjectMap& objects,
                      const VpiObjectMap& unit_typespecs, SimContext& ctx,
                      const VpiAttachBuild& build) {
  if (design == nullptr) return;
  const ParamAttach kWith{unit_typespecs, build, ctx};
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* scope = FindObjectForFlatName(
            objects, prefix.empty() ? std::string(mod->name) : prefix);
        AttachScopeParameters(
            mod, {scope, prefix, objects, VpiDeclOf(*mod), *mod}, kWith);
        AttachScopeSpecParams(mod, prefix, objects);
      });
  for (const PackageDecl* pkg : design->packages) {
    if (pkg == nullptr) continue;
    VpiObject* scope = FindObjectForFlatName(objects, pkg->name);
    if (scope != nullptr) {
      AttachPackageParameters(*pkg, *scope, kWith);
    }
  }
  AttachDefParams(design, objects, ctx, build);
  WalkInstanceObjects(design, objects,
                      [&](const RtlirModule* mod, const std::string& prefix,
                          const VpiObject* instance) {
                        MakeInstanceArrayParamAssigns(
                            *mod, prefix, {objects, ctx, build, mod, instance});
                      });
}

}  // namespace delta
