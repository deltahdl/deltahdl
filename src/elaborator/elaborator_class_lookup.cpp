#include "elaborator/elaborator_class_lookup.h"

#include <cstddef>
#include <string_view>
#include <vector>

#include "elaborator/elaborator_helpers.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

OwnedMember FindMemberAndOwner(const ClassDecl* cls, std::string_view name,
                               const CompilationUnit* unit) {
  for (const auto* c = cls; c;) {
    for (const auto* m : c->members) {
      if (m->name == name) return {m, c};
      // §8.18: a method member carries its name on the method item, not on the
      // ClassMember, so match that too — the local/protected qualifiers live on
      // the ClassMember and must govern method calls just as for data members.
      if (m->method != nullptr && m->method->name == name) return {m, c};
    }
    if (c->base_class.empty()) break;
    c = FindBaseClass(c, unit);
  }
  return {};
}

const ClassMember* FindMemberInClass(const ClassDecl* cls,
                                     std::string_view name,
                                     const CompilationUnit* unit) {
  return FindMemberAndOwner(cls, name, unit).member;
}

const ClassDecl* FindClassInPackage(std::string_view pkg_name,
                                    std::string_view cls_name,
                                    const CompilationUnit* unit) {
  for (const auto* pkg : unit->packages) {
    if (pkg->name != pkg_name) continue;
    for (const auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kClassDecl && item->class_decl &&
          item->class_decl->name == cls_name) {
        return item->class_decl;
      }
    }
  }
  return nullptr;
}

const ClassDecl* FindReferencedClass(const InterfaceRef& ref,
                                     const CompilationUnit* unit) {
  const ClassDecl* in_package = FindClassInPackage(ref.scope, ref.name, unit);
  return in_package != nullptr ? in_package : FindClassDecl(ref.name, unit);
}

const ClassDecl* FindNestedClass(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kClassDecl && m->nested_class &&
        m->nested_class->name == name) {
      return m->nested_class;
    }
  }
  return nullptr;
}

// The identifiers of a `::` chain, left to right: `Outer::Inner` gives
// {Outer, Inner} and `C` gives {C}. Empty where an operand is anything but an
// identifier, a select or a parameterized class among them.
static std::vector<std::string_view> ScopeChainNames(const Expr* prefix) {
  std::vector<std::string_view> names;
  const Expr* e = prefix;
  while (e && e->kind == ExprKind::kMemberAccess && e->is_scope_resolution) {
    if (!e->rhs || e->rhs->kind != ExprKind::kIdentifier) return {};
    names.push_back(e->rhs->text);
    e = e->lhs;
  }
  if (!e || e->kind != ExprKind::kIdentifier) return {};
  names.push_back(e->text);
  return {names.rbegin(), names.rend()};
}

std::vector<const ClassDecl*> ClassChainOfScopePrefix(
    const Expr* prefix, const CompilationUnit* unit) {
  const std::vector<std::string_view> kNames = ScopeChainNames(prefix);
  if (kNames.empty()) return {};
  size_t next = 1;
  const ClassDecl* cls = nullptr;
  if (kNames.size() > 1) {
    cls = FindClassInPackage(kNames[0], kNames[1], unit);
    if (cls) next = 2;
  }
  if (!cls) cls = FindClassDecl(kNames[0], unit);
  std::vector<const ClassDecl*> chain;
  for (; cls; ++next) {
    chain.push_back(cls);
    if (next == kNames.size()) return chain;
    cls = FindNestedClass(cls, kNames[next]);
  }
  return {};
}

// The class a bare name written inside the last class of `chain` resolves to
// among the chain's classes: §8.23 (printed 201) reads it first in that class
// -- the class itself, or one nested in it -- then in each enclosing class
// outward, so `A` inside B nested in Outer is Outer's nested A. Null where no
// class of the chain declares it, which leaves the enclosing scope's classes.
static const ClassDecl* ClassAmongEnclosing(
    std::string_view name, const std::vector<const ClassDecl*>& chain) {
  for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
    if ((*it)->name == name) return *it;
    if (const ClassDecl* nested = FindNestedClass(*it, name)) return nested;
  }
  return nullptr;
}

// The names of a named type, outermost first: each outer prefix, the scope
// and the type, so `A::B::C` gives {A, B, C} and `C` gives {C}.
static std::vector<std::string_view> TypeChainNames(const DataType& dt) {
  std::vector<std::string_view> names = dt.outer_scope_names;
  if (!dt.scope_name.empty()) names.push_back(dt.scope_name);
  names.push_back(dt.type_name);
  return names;
}

const ClassDecl* ClassOfDeclaredType(const DataType& dt,
                                     const std::vector<const ClassDecl*>& chain,
                                     const CompilationUnit* unit) {
  if (dt.kind != DataTypeKind::kNamed) return nullptr;
  const std::vector<std::string_view> kNames = TypeChainNames(dt);
  size_t next = 1;
  const ClassDecl* cls = ClassAmongEnclosing(kNames[0], chain);
  if (cls == nullptr && kNames.size() > 1) {
    cls = FindClassInPackage(kNames[0], kNames[1], unit);
    if (cls != nullptr) next = 2;
  }
  if (cls == nullptr) cls = FindClassDecl(kNames[0], unit);
  for (; cls != nullptr && next < kNames.size(); ++next) {
    cls = FindNestedClass(cls, kNames[next]);
  }
  return cls;
}

}  // namespace delta
