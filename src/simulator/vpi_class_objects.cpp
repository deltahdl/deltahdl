#include "simulator/vpi_class_objects.h"

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_collection_elements.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"

namespace delta {

namespace {

// §37.17 with §8.3: the kind of variable a property declared as `member` is,
// a class var where its type names a class the run knows and an array var
// where it declares unpacked dimensions.
int PropertyVariableKind(const ClassMember& member, SimContext& ctx) {
  if (!member.unpacked_dims.empty()) return vpiArrayVar;
  const DataType& type = member.data_type;
  const bool kNamesClass = type.kind == DataTypeKind::kNamed &&
                           ctx.FindClassType(type.type_name) != nullptr;
  return kNamesClass ? vpiClassVar : VpiDataTypeVariableKind(type.kind);
}

// §37.33 detail 6 with §37.17 detail 24: the variable the property `member`
// of the object `obj` stands as, under the class obj `holder`, automatic or
// static as declared, with the visibility it was declared with and a copy of
// the value the object holds.
void MakePropertyVariable(VpiObject* holder, ClassObject& obj,
                          const ClassMember& member, SimContext& ctx,
                          const VpiAttachBuild& build) {
  VpiObject* var = build.alloc();
  var->type = PropertyVariableKind(member, ctx);
  var->name = build.keep(std::string(member.name));
  var->parent = holder;
  var->automatic = !member.is_static;
  if (member.is_local) {
    var->visibility = vpiLocalVis;
  } else if (member.is_protected) {
    var->visibility = vpiProtectedVis;
  }
  var->property_of = &obj;
  const Logic4Vec* held = VpiHeldPropertyValue(obj, member.name);
  if (held != nullptr) {
    auto* storage = build.arena.Create<Variable>();
    storage->value = MakeLogic4Vec(build.arena, held->width);
    storage->value.is_signed = held->is_signed;
    var->var = storage;
    var->size = static_cast<int>(held->width);
    VpiRefreshElementCopy(*var);
  }
  holder->children.push_back(var);
}

// §8.13: the class `type` and those it extends, the base first. The bound
// stops a chain of extensions that loops.
std::vector<const ClassTypeInfo*> ClassChain(const ClassTypeInfo* type) {
  constexpr int kMaxDepth = 64;
  std::vector<const ClassTypeInfo*> chain;
  for (int depth = 0; depth < kMaxDepth && type != nullptr; ++depth) {
    chain.insert(chain.begin(), type);
    type = type->parent;
  }
  return chain;
}

// §37.32 with §37.31: the class defn of the class `obj` was created with. A
// class a module declares has one under each instance of the module, and the
// object's is the one under the instance it was created in, found among the
// `objects` by that instance's path; any other class has the one `by_decl`
// holds for its declaration, as has a class of the first top.
VpiObject* ClassDefnOf(
    const ClassObject& obj, const VpiObjectMap& objects,
    const std::unordered_map<const void*, VpiObject*>& by_decl) {
  const ClassTypeInfo* type = obj.type;
  if (type == nullptr || type->decl == nullptr) return nullptr;
  std::string_view path = obj.instance;
  if (!path.empty() && path.back() == '.') path.remove_suffix(1);
  VpiObject* scope = type->package.empty() && !path.empty()
                         ? FindObjectForFlatName(objects, path)
                         : nullptr;
  if (scope != nullptr) {
    for (VpiObject* child : scope->children) {
      if (child->type == vpiClassDefn && child->name == type->decl->name) {
        return child;
      }
    }
  }
  auto found = by_decl.find(type->decl);
  return found == by_decl.end() ? nullptr : found->second;
}

}  // namespace

Logic4Vec* VpiHeldPropertyValue(ClassObject& obj, std::string_view name) {
  std::string key(name);
  if (auto cell = obj.ref_cells.find(key); cell != obj.ref_cells.end()) {
    return &cell->second.var->value;
  }
  if (auto own = obj.properties.find(key); own != obj.properties.end()) {
    return &own->second;
  }
  const ClassTypeInfo* declarer =
      obj.type != nullptr ? obj.type->StaticPropertyDeclarer(name) : nullptr;
  if (declarer == nullptr) return nullptr;
  auto found = declarer->static_properties.find(key);
  return found == declarer->static_properties.end() ? nullptr : &found->second;
}

VpiObject* VpiMakeClassObject(ClassObject& obj, VpiObject* defn,
                              SimContext& ctx, const VpiAttachBuild& build) {
  VpiObject* made = build.alloc();
  made->type = vpiClassObj;
  made->obj_id = static_cast<int64_t>(obj.handle);
  if (obj.type == nullptr) return made;
  VpiObject* typespec = build.alloc();
  typespec->type = vpiClassTypespec;
  typespec->name = build.keep(std::string(obj.type->name));
  typespec->parent = made;
  if (defn != nullptr) typespec->children.push_back(defn);
  made->children.push_back(typespec);
  for (const ClassTypeInfo* cls : ClassChain(obj.type)) {
    if (cls->decl == nullptr) continue;
    for (const ClassMember* member : cls->decl->members) {
      if (member != nullptr && member->kind == ClassMemberKind::kProperty &&
          !member->is_param) {
        MakePropertyVariable(made, obj, *member, ctx, build);
      }
    }
  }
  return made;
}

VpiHandle VpiContext::ClassObjectOf(VpiObject& class_var) {
  if (class_var.var == nullptr || sim_ctx_ == nullptr) {
    return class_var.referenced_object;
  }
  VpiRefreshElementCopy(class_var);
  ClassObject* obj = sim_ctx_->GetClassObject(class_var.var->value.ToUint64());
  if (obj == nullptr) return nullptr;
  // §37.33 detail 1: an identifier may be reused once its object is
  // reclaimed, so an object made for one that has since gone is made afresh.
  VpiObject*& made = run_objects_[obj];
  if (made == nullptr || made->obj_id != static_cast<int64_t>(obj->handle)) {
    made = VpiMakeClassObject(
        *obj, ClassDefnOf(*obj, object_map_, run_objects_), *sim_ctx_,
        {[this] { return AllocObject(); },
         [this](std::string name) {
           name_pool_.push_back(std::move(name));
           return std::string_view(name_pool_.back());
         },
         sim_ctx_->GetArena()});
  }
  return made;
}

}  // namespace delta
