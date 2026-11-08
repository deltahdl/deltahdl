#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

VpiObject* GenScopeArrayOf(VpiObject* scope, std::string_view name,
                           const VpiAttachBuild& build) {
  for (VpiObject* child : scope->children) {
    if (child->type == vpiGenScopeArray && child->name == name) return child;
  }
  VpiObject* array = build.alloc();
  array->type = vpiGenScopeArray;
  array->name = build.keep(std::string(name));
  array->full_name = scope->full_name.empty()
                         ? std::string(name)
                         : scope->full_name + "." + std::string(name);
  array->parent = scope;
  scope->children.push_back(array);
  return array;
}

void MakeGenVar(VpiObject* array, std::string_view genvar,
                const VpiAttachBuild& build) {
  for (VpiObject* child : array->children) {
    if (child->type == vpiGenVar) return;
  }
  VpiObject* var = build.alloc();
  var->type = vpiGenVar;
  var->name = build.keep(std::string(genvar));
  var->full_name =
      array->full_name.substr(0, array->full_name.size() - array->name.size()) +
      std::string(genvar);
  var->parent = array;
  array->children.push_back(var);
}

void MakeGenvarParameter(VpiObject* block, std::string_view genvar) {
  VpiObject* param = ChildNamed(block, genvar);
  if (param == nullptr) return;
  param->type = vpiParameter;
  param->local_param = true;
}

void MakeArrayElement(VpiObject* block, VpiObject* array, int64_t index,
                      const VpiAttachBuild& build) {
  block->array_member = true;
  block->index = static_cast<int>(index);
  block->index_expr = VpiIntConstant(index, build);
  if (block->parent == array) return;
  if (block->parent != nullptr) {
    std::erase(block->parent->children, block);
  }
  block->parent = array;
  array->children.push_back(block);
}

VpiObject* BlockNamed(VpiObject* scope, const std::string& name,
                      const VpiAttachBuild& build) {
  if (VpiObject* block = ChildNamed(scope, name)) return block;
  VpiObject* block = build.alloc();
  block->name = build.keep(name);
  block->full_name = scope->full_name + "." + name;
  block->parent = scope;
  scope->children.push_back(block);
  return block;
}

void MakeGenScopes(VpiObject* instance, const HierPath& path,
                   const VpiAttachBuild& build) {
  VpiObject* scope = instance;
  for (const HierStep& step : path) {
    std::string name(step.external_name);
    if (step.has_index) name += "[" + std::to_string(step.index) + "]";
    VpiObject* block = BlockNamed(scope, name, build);
    block->type = vpiGenScope;
    block->implicit_decl = step.name.empty();
    if (step.has_index) {
      VpiObject* array = GenScopeArrayOf(scope, step.external_name, build);
      MakeArrayElement(block, array, step.index, build);
      MakeGenVar(array, step.genvar, build);
      MakeGenvarParameter(block, step.genvar);
    }
    scope = block;
  }
}

void FoldInto(VpiObject* flat, VpiObject* alias) {
  VpiObject* scope = alias->parent;
  if (flat->parent != nullptr) std::erase(flat->parent->children, flat);
  std::replace(scope->children.begin(), scope->children.end(), alias, flat);
  flat->parent = scope;
  flat->name = alias->name;
  flat->full_name = alias->full_name;
  flat->index = alias->index;
}

void Refullname(VpiObject* obj, const std::string& from,
                const std::string& to) {
  const std::string_view kName(obj->full_name);
  if (kName.starts_with(from) &&
      (kName.size() == from.size() ||
       std::string_view(".[:").find(kName[from.size()]) !=
           std::string_view::npos)) {
    obj->full_name = to + obj->full_name.substr(from.size());
  }
  for (VpiObject* child : obj->children) {
    if (child->parent == obj) Refullname(child, from, to);
  }
}

std::string StoredKey(const RtlirModule& mod,
                      const RtlirGenBlockMember& member) {
  if (member.kind == RtlirGenBlockMember::Kind::kStorage) {
    return std::string(member.storage);
  }
  const RtlirParamDecl& param = mod.params[member.param_index];
  return std::string(param.gen_block_prefix) + std::string(param.name);
}

void MoveIntoGenScope(VpiObject* flat, VpiObject* scope, std::string_view name,
                      const VpiNameKeeper& keep) {
  const std::string kFrom = flat->full_name;
  std::erase(flat->parent->children, flat);
  flat->parent = scope;
  flat->name = keep(std::string(name));
  Refullname(flat, kFrom, scope->full_name + "." + std::string(name));
  std::erase(scope->children, ChildNamed(scope, name));
  scope->children.push_back(flat);
}

}  // namespace

void AttachGenBlockInstances(const RtlirDesign* design,
                             const VpiObjectMap& objects,
                             const VpiNameKeeper& keep) {
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        for (const RtlirModuleInst& child : mod->children) {
          if (child.gen_block_path.empty()) continue;
          VpiObject* scope = VpiGenScopeOf(instance, child.gen_block_path);
          VpiObject* flat = FindObjectForFlatName(
              objects, VpiFlatName(prefix, child.inst_name));
          if (scope == nullptr || flat == nullptr) continue;
          MoveIntoGenScope(flat, scope, child.simple_inst_name, keep);
        }
      });
}

void AttachGenBlockStorage(const RtlirDesign* design,
                           const VpiObjectMap& objects) {
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        for (const RtlirGenBlockMember& member : mod->gen_block_members) {
          if (member.kind == RtlirGenBlockMember::Kind::kIndex) continue;
          VpiObject* scope = VpiGenScopeOf(instance, member.gen_block_path);
          VpiObject* alias =
              scope == nullptr ? nullptr : ChildNamed(scope, member.name);
          VpiObject* flat = FindObjectForFlatName(
              objects, VpiFlatName(prefix, StoredKey(*mod, member)));
          if (alias == nullptr || flat == nullptr || alias == flat) continue;
          FoldInto(flat, alias);
        }
      });
}

void AttachGenScopes(const RtlirDesign* design, const VpiObjectMap& objects,
                     const VpiAttachBuild& build) {
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string&, VpiObject* instance) {
        for (const HierPath& path : mod->gen_block_instances) {
          MakeGenScopes(instance, path, build);
        }
      });
}

}  // namespace delta
