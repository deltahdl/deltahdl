#include <cstdint>
#include <string>
#include <string_view>

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_scopes.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.11: the kind of instance array whose elements are instances of `type`,
// 0 for a kind no instance array is drawn for.
int ArrayKindOf(int type) {
  if (type == kVpiModule) return vpiModuleArray;
  if (type == vpiInterface) return vpiInterfaceArray;
  return type == vpiProgram ? vpiProgramArray : 0;
}

// §37.11: the instance array `element` belongs to, held by the scope the
// element stands in and made there the first time it is asked for: named
// after the array, of the kind its elements make it, sized by its range and
// reaching that range (detail 2) and its bounds.
VpiObject* ArrayOf(VpiObject* element, const InstArrayElement& array,
                   const VpiAttachBuild& build) {
  VpiObject* holder = element->parent;
  const int kKind = ArrayKindOf(element->type);
  for (VpiObject* child : holder->children) {
    if (child->type == kKind && child->name == array.name) return child;
  }
  return VpiMakeInstanceArray(holder, kKind, array.name,
                              PackedRange{array.left, array.right}, build);
}

}  // namespace

VpiObject* VpiMakeInstanceArray(VpiObject* holder, int kind,
                                std::string_view name, const PackedRange& range,
                                const VpiAttachBuild& build) {
  VpiObject* made = build.alloc();
  made->type = kind;
  made->name = build.keep(std::string(name));
  made->full_name = VpiScopedFullName(holder, name);
  made->parent = holder;
  made->size = static_cast<int>(range.HighIndex() - range.LowIndex() + 1);
  made->left_range = VpiIntConstant(range.left, build);
  made->right_range = VpiIntConstant(range.right, build);
  VpiObject* dim = build.alloc();
  dim->type = vpiRange;
  dim->parent = made;
  dim->size = made->size;
  dim->left_range = made->left_range;
  dim->right_range = made->right_range;
  made->children.push_back(dim);
  holder->children.push_back(made);
  return made;
}

void VpiAddArrayElement(VpiObject* array, VpiObject* element, int64_t index,
                        const VpiAttachBuild& build) {
  element->array_member = true;
  element->index = static_cast<int>(index);
  element->index_expr = VpiIntConstant(index, build);
  array->children.push_back(element);
}

void AttachInstanceArrays(const RtlirDesign* design,
                          const VpiObjectMap& objects,
                          const VpiAttachBuild& build) {
  // §37.11 with §37.5 detail 2 and §37.6 detail 1: an instance array of
  // modules, interfaces or programs is an object of its own, reaching its
  // elements by their indices, and each element reaches its index. The
  // elaborator expands the array into its elements, which keep their place
  // in the scope around them; nothing made the array or gave them an index.
  WalkInstanceObjects(
      design, objects,
      [&](const RtlirModule* mod, const std::string& prefix, VpiObject*) {
        for (const RtlirModuleInst& inst : mod->children) {
          if (inst.array.name.empty()) continue;
          VpiObject* element = FindObjectForFlatName(
              objects, VpiFlatName(prefix, inst.inst_name));
          if (element == nullptr || element->parent == nullptr ||
              ArrayKindOf(element->type) == 0) {
            continue;
          }
          VpiAddArrayElement(ArrayOf(element, inst.array, build), element,
                             inst.array.index, build);
        }
      });
}

}  // namespace delta
