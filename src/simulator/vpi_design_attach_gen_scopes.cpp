#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
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

// §37.85: the generate block instances the path `path` names below
// `instance`, outermost first, each made the gen scope it is, and each
// iteration of a loop generate an element of its gen scope array. A step
// with no object - an unnamed block, or one declaring nothing the run keys -
// ends the walk.
void MakeGenScopes(VpiObject* instance, const HierPath& path,
                   const VpiAttachBuild& build) {
  VpiObject* scope = instance;
  for (const HierStep& step : path) {
    if (step.name.empty()) return;
    std::string name(step.name);
    if (step.has_index) name += "[" + std::to_string(step.index) + "]";
    VpiObject* block = ChildNamed(scope, name);
    if (block == nullptr) return;
    block->type = vpiGenScope;
    if (step.has_index) {
      MakeArrayElement(block, GenScopeArrayOf(scope, step.name, build),
                       step.index, build);
    }
    scope = block;
  }
}

// A key telling `path` from every other path, which a block holding several
// members is walked once by.
std::string PathKey(const HierPath& path) {
  std::string key;
  for (const HierStep& step : path) {
    key += std::string(step.name) + "[" +
           (step.has_index ? std::to_string(step.index) : "") + "].";
  }
  return key;
}

}  // namespace

void AttachGenScopes(const RtlirDesign* design, const VpiObjectMap& objects,
                     const VpiAttachBuild& build) {
  // §37.85: a generate block instance is a gen scope, and the instances of a
  // loop generate's block are the elements of a gen scope array. The scopes
  // the run's keys made for them were all modules, and no array was made.
  if (design == nullptr || design->top_modules.empty() ||
      design->top_modules.front() == nullptr) {
    return;
  }
  const std::string kFirstTop(design->top_modules.front()->name);
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        VpiObject* instance =
            FindObjectForFlatName(objects, prefix.empty() ? kFirstTop : prefix);
        if (instance == nullptr) return;
        std::unordered_set<std::string> walked;
        for (const RtlirGenBlockMember& member : mod->gen_block_members) {
          if (!walked.insert(PathKey(member.gen_block_path)).second) {
            continue;
          }
          MakeGenScopes(instance, member.gen_block_path, build);
        }
      });
}

}  // namespace delta
