// The order the design's type names and the packages' and the compilation
// unit's data are registered, initialized and constructed in, ahead of every
// module: §26.2 (printed page 808 of IEEE 1800-2023) has a package's
// declaration assignments made before any initial or always procedure starts,
// as a compilation unit's are, §3.12.1 (printed 56) has a module's reference
// searched for in the unit's scope, the names its imports make visible
// included, and §6.21 (printed 132-133) has a module's own variable initialized
// at its declaration. Moved out of lowerer.cpp, which stood at the size the
// assert-no-oversized-source-files job fails at, as the order grew its
// steps.

#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/sim_context.h"

namespace delta {

static void RegisterDesignTypeWidths(const RtlirDesign* design,
                                     SimContext& ctx) {
  for (const auto& [name, width] : design->type_widths) {
    ctx.RegisterTypeWidth(name, width);
  }
  // §6.18: the width says how big the type a name stands for is and the kind
  // says what it is, and only the second tells `typedef string s_t` from a name
  // nothing could size.
  for (const auto& [name, kind] : design->type_kinds) {
    ctx.RegisterTypeKind(name, kind);
  }
  // §6.11.1's default signedness and the `signed` keyword are the third fact a
  // name carries, and the one IsSignedType could not recover with the empty map
  // the simulator was passing it.
  for (const auto& [name, is_signed] : design->type_signed) {
    ctx.RegisterTypeSigned(name, is_signed);
  }
  // §11.5.1's declared range is the fourth, and the one a select of a
  // procedure's or a subroutine body's local of the type asks for: the name is
  // all its declaration carries, and the width addresses it as [width-1:0].
  for (const auto& [name, range] : design->type_ranges) {
    ctx.RegisterTypeRange(name, range);
  }
}

// The design's type names and the packages' and the compilation unit's own
// declarations, registered ahead of every module: RegisterDesignTypeWidths
// for the names, §6.18's typedef chains (RegisterTypeTargets) ahead of every
// class, whose static initialization (§8.9, printed page 186) asks them
// whether a `static mb_t mb = new(K)` is a mailbox -- asked once the
// packages' and the unit's classes were lowered, the copy was built on the
// first reference instead -- and §7.2.1's layouts for the member selects
// that reach a value no variable holds. §26.2: a package variable's declaration
// assignment may call a function of the package or of one it imports and
// name an enumeration constant, and §26.6 (printed pages 815-816) lets it
// read a name another package's export hands on, so the subroutines, the
// constants and the exports are bound before the variables are initialized;
// bound after them, such a read answered 0. §3.12.1 (printed 56) with §26.2
// (printed 808): the compilation unit's data items are initialized before
// any procedure starts as a package's are, and a package names none of the
// unit's while the unit may name a package's, so the unit's storage follows
// the packages' and its initializers (InitCompilationUnitData) follow the
// packages' initializers.
void Lowerer::LowerDesignData() {
  RegisterDesignTypeWidths(design_, ctx_);
  RegisterTypeTargets(design_, ctx_);
  RegisterDesignTypeLayouts(design_, ctx_, arena_);
  RegisterDesignEnumTypes(design_, ctx_, arena_);
  RegisterUnitClassVariables(design_, ctx_, arena_);
  RegisterPackageScopedSubroutines(design_, ctx_, arena_);
  RegisterPackageEnumConstants(design_, ctx_, arena_);
  CreatePackageDataVariables(design_, ctx_, arena_);
  CreateUnitDataVariables(design_, ctx_, arena_);
  AliasPackageExports(design_, ctx_, arena_);
  InitPackageDataVariables(design_, ctx_, arena_);
}

// §26.3 (printed page 810) with §3.12.1 (printed 56): an import written in
// the compilation-unit scope makes the package's names visible in the unit's
// scope, where the unit's own declaration assignments read them, so the
// unit's imports are bound -- each name aliased under its bare key to the
// package's storage, which holds its value once LowerDesignData has run the
// package's initializers -- before the unit's initializers are evaluated,
// and `import p::*; int g = K;` outside every module reads p's K. Bound
// after them, as LowerCompilationUnitClasses bound them, the initializer
// found no K and g read 0. The unit's own items stand under "$unit.name"
// and are reached from the unit's frame (InitScopeDataItems in
// lowerer_package_data.cpp); each module is bound to them as it is lowered
// (AliasUnitDataItems), so a module's own declaration of the name keeps its
// key while the unit's storage survives it (§23.9).
void Lowerer::InitCompilationUnitData() {
  LowerCompilationUnitImports();
  InitUnitDataVariables(design_, ctx_, arena_);
}

// §26.2 (printed page 808) with §6.21 (printed 132-133): the objects the
// packages' and the unit's `C h = new;` declaration assignments construct
// exist before any module's variable is initialized at its declaration, so
// a module's `int y = p1::b.get_n();` reads the package's object. The
// packages' classes are lowered for it here (LowerUnimportedPackageClasses,
// lowerer_import.cpp), the unit's having been lowered by
// LowerCompilationUnitClasses, and the typedef names that denote a class
// (§6.18) are bound to it so a variable declared by one constructs; the names a
// package class leaves unbound until the modules are lowered are bound
// again by RebindStrayPackageClassNames. Constructed after the modules, as
// they were, the package's object was made after the module's initializer
// had called a method on a null handle.
void Lowerer::ConstructDesignData() {
  LowerUnimportedPackageClasses();
  RegisterClassTypeAliases(design_, ctx_);
  ConstructDataClassInitializers(design_, ctx_, arena_);
}

}  // namespace delta
