#include "simulator/vpi_class_typespecs.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <functional>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_class_objects.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// §37.32 details 5, 7, 8 and 11: the kinds of a class defn's children a class
// specialization's typespec reaches as its members: its variables, methods,
// constraints, named events and their arrays, virtual interface vars, and the
// classes it nests, which are its internal scopes.
bool IsSpecializationMember(int type) {
  if (VpiIsVariablesType(type) || VpiIsTaskFuncType(type)) return true;
  switch (type) {
    case vpiConstraint:
    case vpiNamedEvent:
    case vpiNamedEventArray:
    case vpiVirtualInterfaceVar:
    case vpiClassDefn:
      return true;
    default:
      return false;
  }
}

// The typespec of the class specialization `type`, whose class `defn` stands
// for, hung from it without being among its children yet.
VpiObject* MakeSpecialization(const ClassTypeInfo& type, VpiObject* defn,
                              const VpiAttachBuild& build) {
  VpiObject* typespec = build.alloc();
  typespec->type = vpiClassTypespec;
  typespec->name = build.keep(std::string(type.name));
  typespec->parent = defn;
  typespec->children.push_back(defn);
  for (VpiObject* member : defn->children) {
    if (IsSpecializationMember(member->type)) {
      typespec->children.push_back(member);
    }
  }
  const ClassTypespecInfo kInfo = VpiClassTypespecOf(&type);
  for (std::size_t i = 0; i < kInfo.params.size(); ++i) {
    VpiObject* param = VpiMakeObjectParameter(
        typespec, *type.decl, kInfo.params[i], kInfo.param_assigns[i], build);
    VpiObject* assign = build.alloc();
    assign->type = vpiParamAssign;
    assign->parent = typespec;
    assign->children.push_back(param);
    // §37.32 detail 3: a specialization's param assign may answer any object
    // with the value or type the parameter has, which the parameter itself is.
    assign->rhs = param;
    typespec->children.push_back(assign);
  }
  return typespec;
}

// The actual the list `actuals` an extends clause writes gives the parameter
// `name`, the `ordered`th of those a value may be given: one naming it, or
// else the one at that place where the list names none there; null for none.
const DataType* WrittenActual(const std::vector<DataType>& actuals,
                              std::string_view name, std::size_t ordered) {
  const auto kNamed =
      std::ranges::find(actuals, name, &DataType::param_arg_name);
  if (kNamed != actuals.end()) return &*kNamed;
  if (ordered >= actuals.size() || !actuals[ordered].param_arg_name.empty()) {
    return nullptr;
  }
  return &actuals[ordered];
}

// The parameter named `name` among the children of the class defn `defn`,
// null for none.
VpiObject* DefnParameter(const VpiObject& defn, std::string_view name) {
  const auto kFound =
      std::ranges::find_if(defn.children, [name](const VpiObject* child) {
        return (child->type == vpiParameter ||
                child->type == vpiTypeParameter) &&
               child->name == name;
      });
  return kFound == defn.children.end() ? nullptr : *kFound;
}

// The class defn among `defns` the class type `type` is of: for a copy the
// run holds of a class a module declares under a later instance of it, the
// defn under that instance, and otherwise the first defn of its declaration,
// the one under the module's first instance where a module declares it; null
// for none.
VpiObject* DefnOfClass(const VpiClassDefnObjects& defns,
                       const ClassTypeInfo& type) {
  std::string_view scope = type.instance_scope;
  if (scope.ends_with('.')) scope.remove_suffix(1);
  const auto kOwn = defns.find({type.decl, std::string(scope)});
  if (kOwn != defns.end()) return kOwn->second;
  const auto kFirst = defns.lower_bound({type.decl, std::string()});
  return kFirst != defns.end() && kFirst->first.first == type.decl
             ? kFirst->second
             : nullptr;
}

// The built-in classes §37.32's vpiClassType names, by the name each is
// declared with in the std package (§15.3, §15.4, §9.7).
constexpr std::array<std::pair<std::string_view, int>, 3> kBuiltinClasses{{
    {"mailbox", vpiMailboxClass},
    {"semaphore", vpiSemaphoreClass},
    {"process", vpiProcessClass},
}};

}  // namespace

void VpiAttachClassSpecializations(const VpiClassDefnObjects& defns,
                                   SimContext& ctx,
                                   const VpiAttachBuild& build) {
  std::vector<ClassTypeInfo*> types = ctx.RegisteredClassTypes(true);
  std::ranges::sort(types, {}, &ClassTypeInfo::name);
  std::vector<std::pair<const ClassTypeInfo*, VpiObject*>> made;
  for (const ClassTypeInfo* type : types) {
    if (VpiObject* defn = DefnOfClass(defns, *type)) {
      made.emplace_back(type, MakeSpecialization(*type, defn, build));
    }
  }
  for (const auto& [type, typespec] : made) {
    typespec->parent->specializations.push_back(typespec);
    const auto kBase =
        std::ranges::find(made, type->parent,
                          &std::pair<const ClassTypeInfo*, VpiObject*>::first);
    if (kBase != made.end()) typespec->children.push_back(kBase->second);
  }
}

const std::vector<VpiObject*>& VpiClassDefnList(int type,
                                                const VpiObject& defn) {
  return type == vpiDerivedClasses ? defn.derived_classes
                                   : defn.specializations;
}

VpiObject* VpiSpecializationTypespec(const VpiObject& defn,
                                     std::string_view name) {
  const auto kFound =
      std::ranges::find(defn.specializations, name, &VpiObject::name);
  return kFound == defn.specializations.end() ? nullptr : *kFound;
}

void VpiMakeExtendsParamAssigns(
    VpiObject* typespec, const ClassDecl& derived, const ClassDecl& base,
    const std::function<VpiObject*(const Expr*)>& expression,
    const VpiAttachBuild& build) {
  const VpiObject& base_defn = *typespec->children.front();
  std::size_t ordered = 0;
  for (const auto& [name, declared] : base.params) {
    if (base.localparam_port_names.contains(name)) continue;
    const DataType* actual =
        WrittenActual(derived.base_class_type_params, name, ordered++);
    VpiObject* param = DefnParameter(base_defn, name);
    if (param == nullptr) continue;
    VpiObject* assign = build.alloc();
    assign->type = vpiParamAssign;
    assign->parent = typespec;
    assign->children.push_back(param);
    const Expr* value = actual != nullptr ? actual->type_ref_expr : declared;
    assign->rhs = value != nullptr ? expression(value) : nullptr;
    typespec->children.push_back(assign);
  }
}

int VpiClassTypeOf(const VpiObject& typespec) {
  const bool kDeclared = std::ranges::any_of(
      typespec.children,
      [](const VpiObject* child) { return child->type == vpiClassDefn; });
  const auto kBuiltin =
      std::ranges::find(kBuiltinClasses, std::string_view(typespec.name),
                        &std::pair<std::string_view, int>::first);
  if (kDeclared || kBuiltin == kBuiltinClasses.end()) {
    return vpiUserDefinedClass;
  }
  return kBuiltin->second;
}

VpiHandle VpiClassTypespecBase(const VpiObject& typespec) {
  const auto kBase =
      std::ranges::find(typespec.children, vpiClassTypespec, &VpiObject::type);
  return kBase == typespec.children.end() ? nullptr : *kBase;
}

}  // namespace delta
