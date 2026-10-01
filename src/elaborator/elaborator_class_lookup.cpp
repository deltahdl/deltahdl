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

const ClassMember* FindMemberInClass(const ClassDecl* cls,
                                     std::string_view name,
                                     const CompilationUnit* unit) {
  for (const auto* c = cls; c;) {
    for (const auto* m : c->members) {
      if (m->name == name) return m;
      // §8.18: a method member carries its name on the method item, not on the
      // ClassMember, so match that too — the local/protected qualifiers live on
      // the ClassMember and must govern method calls just as for data members.
      if (m->method != nullptr && m->method->name == name) return m;
    }
    if (c->base_class.empty()) break;
    c = FindClassDecl(c->base_class, unit);
  }
  return nullptr;
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

const ClassDecl* ClassOfDeclaredType(const DataType& dt,
                                     const std::vector<const ClassDecl*>& chain,
                                     const CompilationUnit* unit) {
  if (dt.kind != DataTypeKind::kNamed) return nullptr;
  if (dt.scope_name.empty()) {
    if (const ClassDecl* c = ClassAmongEnclosing(dt.type_name, chain)) return c;
    return FindClassDecl(dt.type_name, unit);
  }
  if (const ClassDecl* outer = ClassAmongEnclosing(dt.scope_name, chain)) {
    return FindNestedClass(outer, dt.type_name);
  }
  if (const ClassDecl* in_pkg =
          FindClassInPackage(dt.scope_name, dt.type_name, unit)) {
    return in_pkg;
  }
  const ClassDecl* outer = FindClassDecl(dt.scope_name, unit);
  return outer ? FindNestedClass(outer, dt.type_name) : nullptr;
}

}  // namespace delta
