#include <string_view>
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

// §6.18 (printed page 118) lets a forward typedef, `typedef struct pair_t;`,
// stand for a definition the same scope gives before or after the reference,
// and §23.9 (printed 761) resolves a function's or a task's names outward to
// the module's, so a module subroutine written between the forward typedef
// and the definition names pair_t lawfully in a formal. The subroutine was
// resolved once, by Elaborator::ElaborateBehavioralItem against the table as
// it stood at the item, where the forward name holds a placeholder with no
// members, so `pair_t A` of `function int f(union tagged { void N; pair_t A;
// } a)` was left unresolved, the formal sized as a scalar, and `f(tagged A
// '{3, 4})` read 0 for §7.2.1's 34; a task's output formal of the same shape
// wrote 0 the same way, while a class's method between the two was resolved
// again by ResolveModuleClassFormalTypes. Every function and task among
// `items`, the module's own, is resolved again against `typedefs`, the
// module's table once the item walk has reached every definition; a member
// resolved at the item resolves to the same type again. Elaborator::
// ElaborateItems calls it after the item loop, beside the class pass, and
// ResolveScopeSubroutineFormalTypes takes a package's and the unit's
// subroutines through it.
//
// §27.3 (printed page 818) has a generate block's items act as a module's own
// would, the enclosing scope's declarations reached directly, and §27.5
// (printed 824) makes each block a scope of its own, so a subroutine written
// in a block between the module's forward typedef and its definition names
// pair_t as a module subroutine does. Elaborator::ElaborateBehavioralItem
// queues the block for Elaborator::ProcessPendingGenerate with the table as
// it stood at the construct, the placeholder and no definition, and resolved
// the block's subroutine once against that copy, so `g.f(tagged A '{3, 4})`
// read 0 while the module's own `f` read 34 -- 84eea0a11's remainder. The
// walk now descends into a conditional generate's body and each of its else
// arms, a case generate's arms and a loop generate's body, before the pending
// pass runs, and the pending pass then finds each member resolved.
//
// §6.18 also lets a generate block forward-declare a typedef of its own and
// define it below the block's subroutine, and that definition enters the
// table only as Elaborator::ElaborateGenerateItems reaches it, after the
// module's pass and after the block's subroutine was resolved at its item, so
// `g.f(tagged A '{3, 4})` still read 0 with the forward typedef and the
// definition both written in g -- ca0c213d4's remainder. That site now calls
// this again once the block's items are walked, with the table as the walk
// leaves it, and the descent reaches the blocks nested in the block.
void ResolveModuleSubroutineFormalTypes(const std::vector<ModuleItem*>& items,
                                        const TypedefMap& typedefs,
                                        Arena& arena) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      ResolveFormalAggregateTypes(item, typedefs, arena);
      continue;
    }
    ResolveModuleSubroutineFormalTypes(item->gen_body, typedefs, arena);
    if (item->gen_else != nullptr) {
      ResolveModuleSubroutineFormalTypes({item->gen_else}, typedefs, arena);
    }
    for (const auto& arm : item->gen_case_items) {
      ResolveModuleSubroutineFormalTypes(arm.body, typedefs, arena);
    }
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
// each class as it is reached, and again by ResolveModuleSubroutineFormalTypes
// and ResolveModuleClassFormalTypes once the walk is done.
void ResolveScopeSubroutineFormalTypes(const std::vector<ModuleItem*>& items,
                                       const TypedefMap& typedefs,
                                       Arena& arena) {
  ResolveModuleSubroutineFormalTypes(items, typedefs, arena);
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr) {
      ResolveClassMethodFormalTypes(item->class_decl, typedefs, arena);
    }
  }
}

// §26.3 (printed page 808) lets a package's items name another package's
// declaration through its qualifier, `q::pair_t Add` in p's function, while
// §26.2 (printed 808) keeps the compilation-unit scope's own declarations out
// of a package's reach. The unit's table holds a package typedef under the
// "q::pair_t" key RegisterPackageTypedefs records and the unit's own under
// bare names, so the table a package resolves by starts from the keys whose
// prefix names a package of `unit` and nothing else; a package's table began
// from nothing and left `q::pair_t` a name it could not answer.
TypedefMap PackageQualifiedTypedefs(const CompilationUnit* unit,
                                    const TypedefMap& typedefs) {
  TypedefMap qualified;
  for (const auto& [key, type] : typedefs) {
    auto sep = key.find("::");
    if (sep == std::string_view::npos) continue;
    for (const auto* pkg : unit->packages) {
      if (pkg->name != key.substr(0, sep)) continue;
      qualified.emplace(key, type);
      break;
    }
  }
  return qualified;
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
// filled it, the packages' and the classes' qualified names included, of
// which a package sees the packages' (§26.3, PackageQualifiedTypedefs).
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
  const TypedefMap kQualified = PackageQualifiedTypedefs(unit, typedefs);
  for (auto* pkg : unit->packages) {
    ResolveScopeSubroutineFormalTypes(
        pkg->items, DpiScopeTypedefs(pkg->items, unit, kQualified), arena);
  }
  TypedefMap unit_typedefs = DpiScopeTypedefs(unit->cu_items, unit, typedefs);
  ResolveScopeSubroutineFormalTypes(unit->cu_items, unit_typedefs, arena);
  for (auto* cls : unit->classes) {
    ResolveClassMethodFormalTypes(cls, unit_typedefs, arena);
  }
}

}  // namespace delta
