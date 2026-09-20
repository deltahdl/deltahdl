#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator_dpi_names.h"
#include "elaborator/elaborator_items_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// §13.3 (printed page 337) declares a formal with any data_type, a structure
// or union written inline in the declaration among them, and §7.2.1 (printed
// 147) lays such a type out member by member, a member naming a typedef of an
// aggregate of its own included. The simulator sizes and lays a formal out
// from the declaration's DataType alone, with no typedef table in reach, and
// ResolvedAggregateType resolves a variable's or a port's members for it
// before lowering while a formal's were left as parsed: `pair_t Add` of
// `function int f(union tagged { void None; pair_t Add; } a)` carried no
// nested type, so the formal was sized as if the member were a scalar and
// `a.Add.a` in the body reached no member. Each formal's inline aggregate is
// resolved in place on the declaration against the typedefs the declaration
// sees; a formal of any other type has no member to resolve, and one resolved
// by an earlier elaboration of the same declaration resolves to the same
// types again.
void ResolveFormalAggregateTypes(ModuleItem* item, const TypedefMap& typedefs,
                                 Arena& arena) {
  for (FunctionArg& arg : item->func_args) {
    ResolveNestedAggregateTypes(arg.data_type, typedefs, arena);
  }
}

namespace {

// §8.23 (printed page 200): a class is a scope that nests in the one it is
// written in, and a typedef its body declares stands by its bare name inside
// the class, over those of the enclosing scope, `outer`.
TypedefMap ClassScopeTypedefs(const ClassDecl* cls, const TypedefMap& outer) {
  TypedefMap typedefs = outer;
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kTypedef || m->typedef_item == nullptr)
      continue;
    typedefs[m->name] = m->typedef_item->typedef_type;
  }
  return typedefs;
}

// §13.3 and §7.2.1: the inline aggregate formals of every subroutine among
// `items`, and of every method of a class declared among them, resolved
// against `typedefs`, the table of the scope the items stand in. A package's
// items and the compilation unit's take this walk; a module's and an
// interface's own items are walked by Elaborator::ElaborateBehavioralItem and
// Elaborator::ElaborateModuleClassDecl, which resolve each subroutine and
// each class as it is reached.
void ResolveScopeSubroutineFormalTypes(const std::vector<ModuleItem*>& items,
                                       const TypedefMap& typedefs,
                                       Arena& arena) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      ResolveFormalAggregateTypes(item, typedefs, arena);
    } else if (item->kind == ModuleItemKind::kClassDecl &&
               item->class_decl != nullptr) {
      ResolveClassMethodFormalTypes(item->class_decl, typedefs, arena);
    }
  }
}

}  // namespace

// §8.6 (printed page 183) has an object's method called as its properties are
// read, and the method's formal is declared under §13.3 as a module
// subroutine's is; §8.23's example types a method's formal by the class's own
// typedef, `radix r`. A class's methods resolved by nothing: the class's
// members are walked by no ModuleItem loop, so a method taking `union tagged
// { void None; pair_t Add; } a` was sized as if Add were a scalar and
// `h.f(tagged Add '{3, 4})` read 0 from `a.Add.a * 10 + a.Add.b` where
// §7.2.1 places 3 and 4, 34. A class nested in the class sees the class's
// typedefs in turn (§8.23).
void ResolveClassMethodFormalTypes(ClassDecl* cls, const TypedefMap& outer,
                                   Arena& arena) {
  TypedefMap typedefs = ClassScopeTypedefs(cls, outer);
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      ResolveFormalAggregateTypes(m->method, typedefs, arena);
    } else if (m->kind == ClassMemberKind::kClassDecl &&
               m->nested_class != nullptr) {
      ResolveClassMethodFormalTypes(m->nested_class, typedefs, arena);
    }
  }
}

// §6.18 (printed page 118) has a user-defined type's declaration precede
// every reference to its name, and lets a forward typedef, `typedef pair_t;`,
// stand for a definition the same scope gives before or after the reference.
// A class declared between the two is resolved by
// Elaborator::ElaborateModuleClassDecl against the table as it stands at the
// class, where the forward name holds a placeholder with no members, so the
// member `pair_t A` of a method's `union tagged { void N; pair_t A; } a` was
// left unresolved and `h.f(tagged A '{3, 4})` read 0 for §7.2.1's 34. Every
// class the module's walk recorded, `classes`, is resolved again once the
// walk has given the table the definition; a member resolved at the class
// resolves to the same type again, and the class's own typedefs stand over
// the module's as before (§8.23). Elaborator::ElaborateItems calls it after
// the item loop, with the module's class_decls.
void ResolveModuleClassFormalTypes(const std::vector<ClassDecl*>& classes,
                                   const TypedefMap& typedefs, Arena& arena) {
  for (auto* cls : classes) {
    if (cls != nullptr) ResolveClassMethodFormalTypes(cls, typedefs, arena);
  }
}

// §26.2 (printed page 808) has a package's items reference what the package
// declares or imports and nothing the compilation-unit scope declares, so a
// package's subroutines and the methods of its classes resolve their formals
// against the package's own typedefs and its imports' alone; §3.12.1 gives a
// compilation-unit subroutine or class the unit's typedefs and imports, and
// `typedefs` is the unit's table as Elaborator::RegisterCuScopeItems has
// filled it, the packages' and the classes' qualified names included.
// DpiScopeTypedefs adds a scope's own typedefs and its imports' to a table
// for §35.5.6's check, which is the table a formal of the scope resolves by
// too. A package function's `pair_t Add` in `function int f(union tagged {
// void None; pair_t Add; } a)` was resolved by nothing, since the package is
// not a module and ElaborateBehavioralItem never reaches it, so the simulator
// sized the formal as if Add were a scalar and `p::f(tagged Add '{3, 4})`
// read 0 from `a.Add.a * 10 + a.Add.b` where §7.2.1 places 3 and 4, 34. The
// parser keeps a class declared outside every design element in
// unit->classes, apart from cu_items (§3.12.1), so both lists are walked.
void ResolveUnitScopeFormalTypes(CompilationUnit* unit,
                                 const TypedefMap& typedefs, Arena& arena) {
  const TypedefMap kNone;
  for (auto* pkg : unit->packages) {
    ResolveScopeSubroutineFormalTypes(
        pkg->items, DpiScopeTypedefs(pkg->items, unit, kNone), arena);
  }
  TypedefMap unit_typedefs = DpiScopeTypedefs(unit->cu_items, unit, typedefs);
  ResolveScopeSubroutineFormalTypes(unit->cu_items, unit_typedefs, arena);
  for (auto* cls : unit->classes) {
    ResolveClassMethodFormalTypes(cls, unit_typedefs, arena);
  }
}

}  // namespace delta
