#pragma once

#include <string_view>
#include <vector>

#include "simulator/vpi_design_attach_build.h"

namespace delta {

class SimContext;
struct Expr;
struct ModuleItem;
struct RtlirAssertionItemDecl;
struct RtlirDesign;
struct RtlirImport;
struct VpiObject;

// Where a property decl is built: `scope`, the instance or the generate block
// instance declaring it; the typespecs AttachTypespecs answered, the
// compilation unit's and the packages', which a formal's type may name; the
// run its packed dimensions are evaluated in; and the imports of the module
// declaring it, through which a formal's type may name a package's typedef.
struct VpiPropertyDeclSite {
  VpiObject* scope;
  const VpiObjectMap& unit_typespecs;
  SimContext& ctx;
  const std::vector<RtlirImport>& imports;
};

// §37.12 and §37.51: the property decl of the property `declared` stands
// for, hung from the scope declaring it, `at.scope` or the clocking block it
// holds that declares it, with its formals, their typespecs and its
// variables, each built through `with`. VpiFillAssertionItemDeclBody gives it
// its property spec.
VpiObject* VpiMakePropertyDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with);

// §37.12 and §37.53: the sequence decl of the sequence `declared` stands for,
// hung from the scope declaring it, `at.scope` or the clocking block it holds
// that declares it, with its formals, their typespecs and its variables, each
// built through `with`. VpiFillAssertionItemDeclBody gives it its body.
VpiObject* VpiMakeSequenceDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with);

// §37.51 to §37.53: give `made`, the property decl or sequence decl `decl`
// stands as, the property spec or the body `decl` declares, built through
// `with`, once every property and sequence of the scope, which the body may
// instantiate, is declared (§16.8, §16.12).
void VpiFillAssertionItemDeclBody(VpiObject* made, const ModuleItem& decl,
                                  const VpiStmtBuild& with);

// §16.8, §16.8.2 and §16.12 with §37.15: what the formals of `decl`, which
// `made` stands as, are where its body names them, held by an object of no
// kind of its own hung below `made`, for a body to be built with its names
// found there first, then among `made`'s variables (§16.10) and in the
// scopes around it: a ref obj named after each formal, bound to no actual
// since no instance binds one in the declaration (§37.15 detail 3), and a
// variable of its type, resolved in `ctx`, for a local variable formal.
VpiObject* VpiFormalNames(VpiObject* made, const ModuleItem& decl,
                          const SimContext& ctx, const VpiAttachBuild& build);

// §11.12 with §37.12 and §37.57: the let decl the let declaration `item`
// stands as, hung from `scope`, named after it, with a seq formal decl per
// formal in the order declared. VpiFillLetDecl gives the formals their
// defaults and the let decl its body.
VpiObject* VpiMakeLetDecl(const ModuleItem& item, VpiObject* scope,
                          const VpiAttachBuild& build);

// §11.12 with §37.15: what the formals of the let `item`, which `made`
// stands as, are where its body names them, held as VpiFormalNames holds a
// sequence's: a ref obj named after each, bound to no actual, since §11.12
// has each use of the let put its own actual in the formal's place.
VpiObject* VpiLetFormalNames(VpiObject* made, const ModuleItem& item,
                             const VpiAttachBuild& build);

// §37.57: give `made`, the let decl VpiMakeLetDecl made for the let
// declaration `item`, the default each formal declares and the body, built
// through `with`.
void VpiFillLetDecl(VpiObject* made, const ModuleItem& item,
                    const VpiStmtBuild& with);

// What a property or sequence instance names: `type`, vpiPropertyDecl or
// vpiSequenceDecl, the kind of declaration; `name`, written through the
// package path `package`, `pk::s`, where that is not empty; and `scope`, where
// the instance is written.
struct VpiAssertionDeclName {
  const VpiObject* scope;
  int type;
  std::string_view package;
  std::string_view name;
};

// §37.51 and §37.53 with §37.12 and §26.3: the declaration `named` names:
// through a package path, the one that package declares; and otherwise the
// one its scope or a scope standing around it declares, the nearest from a
// generate block instance out to the instance, `cb.s` the one the clocking
// block or interface instance `cb` holds, or else the one a package declares
// that one of `imports` makes visible, among the package objects `objects`
// keys; null where none is.
VpiObject* VpiAssertionDeclNamed(const VpiAssertionDeclName& named,
                                 const std::vector<RtlirImport>& imports,
                                 const VpiObjectMap& objects);

// §16.8 and §16.12 with §37.10 detail 1: give each package a sequence decl per
// sequence and a property decl per property it declares, as
// VpiMakeSequenceDecl and VpiMakePropertyDecl make them, with
// `unit_typespecs`, the typespecs AttachTypespecs answered, for their
// formals' types to name.
void AttachPackageAssertionItemDecls(const RtlirDesign& design,
                                     const VpiObjectMap& objects,
                                     const VpiObjectMap& unit_typespecs,
                                     SimContext& ctx,
                                     const VpiAttachBuild& build);

// §37.51: the property inst the spec `instance` writes, an instance of a
// declared property, hung from the assertion `holder`, reaching the property
// decl of that name where the assertion stands, its arguments and the
// condition `disable` it is disabled under, each built through `with`.
VpiObject* VpiMakePropertyInst(VpiObject* holder, const Expr& instance,
                               const Expr* disable, const VpiStmtBuild& with);

// §37.52: the property expr the Boolean operand `operand` of a property
// stands as: a property inst where it names a property a declaration where it
// stands makes visible (§16.12), and otherwise the sequence expr
// VpiSequenceOperandObject makes of it.
VpiObject* VpiPropertyOperandObject(const Expr& operand,
                                    const VpiStmtBuild& with);

// §37.54: the sequence expr the operand `operand` of a sequence or a sequence
// event (§9.4.2.4) stands as: a sequence inst where it names a sequence a
// declaration where it stands makes visible, and otherwise the expression it
// is, each built through `with`.
VpiObject* VpiSequenceOperandObject(const Expr& operand,
                                    const VpiStmtBuild& with);

}  // namespace delta
