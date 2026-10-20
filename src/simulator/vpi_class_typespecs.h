#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_object.h"

// §37.32: the class typespecs that stand for class specializations, which a
// class defn reaches through vpiClassTypespec and a class obj stands as, and
// the relations and properties §37.32 draws on a class typespec beyond those
// a lexical one has.

namespace delta {

class SimContext;
struct ClassDecl;
struct DataType;
struct Expr;

// §37.32 details 1 and 10: a class typespec per class specialization of the
// class each defn of `defns` stands for -- each class type the run `ctx` holds
// of that class's declaration, its own being §8.25.1's default one -- made
// with `build` and held in the defn's list of specializations, which
// vpiClassTypespec iterates, in the order of their names. Each reaches the
// defn, the defn's variables, methods, constraints, named events and their
// arrays, virtual interface vars and nested classes (details 5, 7, 8, 11), a
// parameter per parameter of the class holding the value the specialization
// gives it (detail 12), a param assign per parameter whose vpiRhs is that
// parameter (detail 3), and the typespec of the specialization it extends, its
// base, which detail 9 makes a specialization too.
void VpiAttachClassSpecializations(const VpiClassDefnObjects& defns,
                                   SimContext& ctx,
                                   const VpiAttachBuild& build);

// §37.31: the class defn among `defns` made for the class `decl` under the
// innermost gen scope around the object `around` that has one, a generate
// block's class having one under each instance of the block (§27.4); else the
// one made in the scope keyed `scope`, else the first made for `decl`, under
// a module's first instance or a generate block's; null for none.
VpiObject* VpiClassDefnOf(const VpiClassDefnObjects& defns,
                          const ClassDecl* decl, const std::string& scope,
                          const VpiObject* around);

// §37.31 detail 5 and §37.32 detail 10: the list the class defn `defn` keeps
// apart from its children that the iteration `type` reaches, its derived
// classes for vpiDerivedClasses and else its class specializations.
const std::vector<VpiObject*>& VpiClassDefnList(int type,
                                                const VpiObject& defn);

// §37.32 detail 1: the class specialization typespec of the class type named
// `name` among those the class defn `defn` holds; null for none.
VpiObject* VpiSpecializationTypespec(const VpiObject& defn,
                                     std::string_view name);

// §37.32 detail 3: the param assigns of the class typespec `typespec` the
// extends clause of `derived` writes, a lexical construct naming a
// specialization of `base`, whose class defn is the typespec's first child:
// one per parameter of `base`'s parameter port list a value may be given,
// reaching it through vpiLhs and, through vpiRhs, the expression `expression`
// makes of the value the clause gives it, by name or in order, or else of the
// default it was declared with; for a type parameter, a typespec of the type
// the clause gives, or of its default type, where that is written as a
// keyword; one written as a name is left to VpiAssignExtendsNamedTypes.
void VpiMakeExtendsParamAssigns(
    VpiObject* typespec, const ClassDecl& derived, const ClassDecl& base,
    const std::function<VpiObject*(const Expr*)>& expression,
    const VpiAttachBuild& build);

// §37.32 detail 3: gives each param assign VpiMakeExtendsParamAssigns made
// on `typespec` for a type parameter whose type, the one the clause gives or
// else its default type, is written as a name, the typespec `named` finds for
// that type, hung from the assign it is given. The typespecs a name finds,
// those of the typedefs, are made after the class defns are, so this runs
// once they are.
void VpiAssignExtendsNamedTypes(
    VpiObject* typespec, const ClassDecl& derived, const ClassDecl& base,
    const std::function<VpiObject*(const DataType&, VpiObject*)>& named);

// §37.32: the vpiClassType of the class typespec `typespec`: the built-in
// mailbox, semaphore or process class, none of which has a declaration
// (detail 13), or else a user-defined class.
int VpiClassTypeOf(const VpiObject& typespec);

// §37.32 detail 9: the class typespec `typespec` extends, null for none.
VpiHandle VpiClassTypespecBase(const VpiObject& typespec);

}  // namespace delta
