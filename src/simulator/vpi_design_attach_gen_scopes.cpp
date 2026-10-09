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

// §37.85: the gen scope array `scope` holds for the loop generate block
// `name`, made under it the first time it is asked for.
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

// §37.85: `block`, a gen scope of an iteration of a loop generate, as an
// element of the gen scope array `array`, reached by its index - the value
// of the loop's genvar in the iteration, which vpiIndex reaches as a constant
// (§38.19) - and moved from the scope it hung in to the array.
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

// §37.85: the block instance `scope` holds under `name`, made where the run
// keyed nothing the block declares, whatever it declares.
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

// §37.85: the generate block instances the path `path` names below
// `instance`, outermost first, each made the gen scope it is, and each
// iteration of a loop generate an element of its gen scope array. A step of
// an unnamed block ends the walk (#5737).
void MakeGenScopes(VpiObject* instance, const HierPath& path,
                   const VpiAttachBuild& build) {
  VpiObject* scope = instance;
  for (const HierStep& step : path) {
    if (step.name.empty()) return;
    std::string name(step.name);
    if (step.has_index) name += "[" + std::to_string(step.index) + "]";
    VpiObject* block = BlockNamed(scope, name, build);
    block->type = vpiGenScope;
    if (step.has_index) {
      MakeArrayElement(block, GenScopeArrayOf(scope, step.name, build),
                       step.index, build);
    }
    scope = block;
  }
}

// §27.4 with §37.17: `flat`, the object of a declaration of a generate block
// instance the run keys under a flattened name, `g_1_v`, put in the place of
// `alias`, the object the block's own name for it, `g[1].v`, made: named as
// declared, under the gen scope, and full-named through it. The passes before
// resolved the block's expressions to `flat`, and it holds what they built.
void FoldInto(VpiObject* flat, VpiObject* alias) {
  VpiObject* scope = alias->parent;
  if (flat->parent != nullptr) std::erase(flat->parent->children, flat);
  std::replace(scope->children.begin(), scope->children.end(), alias, flat);
  flat->parent = scope;
  flat->name = alias->name;
  flat->full_name = alias->full_name;
  flat->index = alias->index;
}

}  // namespace

void AttachGenBlockStorage(const RtlirDesign* design,
                           const VpiObjectMap& objects) {
  // §27.4: a variable or net a generate block instance declares is named
  // under that instance's gen scope. The run keys it under a flattened name
  // and its alias under the block's, and an object was made for each.
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix,
          VpiObject* instance) {
        for (const RtlirGenBlockMember& member : mod->gen_block_members) {
          if (member.kind != RtlirGenBlockMember::Kind::kStorage) continue;
          VpiObject* scope = VpiGenScopeOf(instance, member.gen_block_path);
          VpiObject* alias =
              scope == nullptr ? nullptr : ChildNamed(scope, member.name);
          VpiObject* flat = FindObjectForFlatName(
              objects, VpiFlatName(prefix, member.storage));
          if (alias == nullptr || flat == nullptr || alias == flat) continue;
          FoldInto(flat, alias);
        }
      });
}

void AttachGenScopes(const RtlirDesign* design, const VpiObjectMap& objects,
                     const VpiAttachBuild& build) {
  // §37.85: a generate block instance is a gen scope, and the instances of a
  // loop generate's block are the elements of a gen scope array. The scopes
  // the run's keys made for them were all modules, no array was made, and a
  // block declaring nothing the run keys had no object at all.
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string&, VpiObject* instance) {
        for (const HierPath& path : mod->gen_block_instances) {
          MakeGenScopes(instance, path, build);
        }
      });
}

}  // namespace delta
