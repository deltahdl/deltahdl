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
        const bool kParameter =
            child->type == vpiParameter || child->type == vpiTypeParameter;
        return kParameter && child->name == name;
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
  const bool kOfDecl =
      kFirst != defns.end() && kFirst->first.first == type.decl;
  return kOfDecl ? kFirst->second : nullptr;
}

// §37.32 detail 3: what the extends clause of a derived class gives one
// parameter `name` of its base a value may be given: the actual it writes,
// null for none, and the parameter's default, an expression `declared` for a
// value parameter and a type `declared_type` for a type parameter.
struct ExtendsParam {
  std::string_view name;
  const DataType* actual = nullptr;
  const Expr* declared = nullptr;
  const DataType* declared_type = nullptr;
};

// What the extends clause of `derived` gives each parameter of `base`'s
// parameter port list a value may be given, by name or in order.
std::vector<ExtendsParam> ExtendsParams(const ClassDecl& derived,
                                        const ClassDecl& base) {
  std::vector<ExtendsParam> params;
  std::size_t ordered = 0;
  for (std::size_t i = 0; i < base.params.size(); ++i) {
    const auto& [name, declared] = base.params[i];
    if (base.localparam_port_names.contains(name)) continue;
    params.push_back(
        {name, WrittenActual(derived.base_class_type_params, name, ordered++),
         declared,
         i < base.param_types.size() ? &base.param_types[i] : nullptr});
  }
  return params;
}

// The type `param` is assigned: the type the clause writes for it, or else
// the default type it was declared with; null where it is assigned an
// expression or nothing.
const DataType* AssignedType(const ExtendsParam& param) {
  if (param.actual != nullptr) {
    return param.actual->type_ref_expr == nullptr ? param.actual : nullptr;
  }
  return param.declared == nullptr ? param.declared_type : nullptr;
}

// §37.32 detail 3: a typespec of the type `type` writes as a keyword, of that
// keyword's kind; null for a type written as a name, whose typespec is made
// after the class defns are (VpiAssignExtendsNamedTypes).
VpiObject* KeywordTypespec(const DataType& type, const VpiAttachBuild& build) {
  const int kKind = VpiTypespecKind(type.kind);
  if (kKind == 0) return nullptr;
  VpiObject* typespec = build.alloc();
  typespec->type = kKind;
  return typespec;
}

// §37.32 detail 3: what a lexical typespec's param assign of `param` reaches
// through vpiRhs: the expression `expression` makes of the value the clause
// writes for a value parameter, or else of its default; or a typespec of the
// type it is assigned for a type parameter.
VpiObject* AssignedValue(
    const ExtendsParam& param,
    const std::function<VpiObject*(const Expr*)>& expression,
    const VpiAttachBuild& build) {
  if (const DataType* type = AssignedType(param)) {
    return KeywordTypespec(*type, build);
  }
  const Expr* written =
      param.actual != nullptr ? param.actual->type_ref_expr : param.declared;
  return written == nullptr ? nullptr : expression(written);
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
  for (const ExtendsParam& written : ExtendsParams(derived, base)) {
    VpiObject* param = DefnParameter(base_defn, written.name);
    if (param == nullptr) continue;
    VpiObject* assign = build.alloc();
    assign->type = vpiParamAssign;
    assign->parent = typespec;
    assign->children.push_back(param);
    assign->rhs = AssignedValue(written, expression, build);
    typespec->children.push_back(assign);
  }
}

void VpiAssignExtendsNamedTypes(
    VpiObject* typespec, const ClassDecl& derived, const ClassDecl& base,
    const std::function<VpiObject*(const DataType&, VpiObject*)>& named) {
  for (const ExtendsParam& written : ExtendsParams(derived, base)) {
    const DataType* type = AssignedType(written);
    if (type == nullptr || type->kind != DataTypeKind::kNamed) continue;
    for (VpiObject* assign : typespec->children) {
      if (assign->type == vpiParamAssign &&
          assign->children.front()->name == written.name) {
        assign->rhs = named(*type, assign);
      }
    }
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
