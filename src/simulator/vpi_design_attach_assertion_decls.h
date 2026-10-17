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
// holds that declares it, with its formals, their typespecs, its variables
// and its property spec, each built through `with`.
VpiObject* VpiMakePropertyDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with);

// §37.12 and §37.53: the sequence decl of the sequence `declared` stands for,
// hung from the scope declaring it, `at.scope` or the clocking block it holds
// that declares it, with its formals, their typespecs and its variables, each
// built through `with`. VpiFillSequenceDeclBody gives it its body, once every
// sequence of the scope, which the body may instantiate, is declared (§16.8).
VpiObject* VpiMakeSequenceDecl(const RtlirAssertionItemDecl& declared,
                               const VpiPropertyDeclSite& at,
                               const VpiStmtBuild& with);

// §37.53: give the sequence decl `sequence` the body `decl` declares it with,
// built through `with`, which vpiExpr reaches.
void VpiFillSequenceDeclBody(VpiObject* sequence, const ModuleItem& decl,
                             const VpiStmtBuild& with);

// §26.3 with §37.51: the property decl named `name` a package declares that
// one of `imports` makes visible, among the property decls of the package
// objects `objects` keys; null where no import reaches one.
VpiObject* VpiImportedPropertyDecl(std::string_view name,
                                   const std::vector<RtlirImport>& imports,
                                   const VpiObjectMap& objects);

// §26.3 with §37.53: the sequence decl named `name` a package declares that
// one of `imports` makes visible, among the sequence decls of the package
// objects `objects` keys; null where no import reaches one.
VpiObject* VpiImportedSequenceDecl(std::string_view name,
                                   const std::vector<RtlirImport>& imports,
                                   const VpiObjectMap& objects);

// §37.53 with §37.12: the sequence decl named `name` that `scope` or a scope
// standing around it declares, the nearest from a generate block instance
// out to the instance, `cb.s` the one the clocking block or interface
// instance `cb` holds; null where none was built.
VpiObject* VpiSequenceDeclAround(const VpiObject* scope, std::string_view name);

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
// decl of that name the scope around `holder` declares and its arguments, each
// built through `with`.
VpiObject* VpiMakePropertyInst(VpiObject* holder, const Expr& instance,
                               const VpiStmtBuild& with);

// §37.54: the sequence expr the operand `operand` of a sequence or a sequence
// event (§9.4.2.4) stands as: a sequence inst where it names a sequence a
// declaration where it stands makes visible, and otherwise the expression it
// is, each built through `with`.
VpiObject* VpiSequenceOperandObject(const Expr* operand,
                                    const VpiStmtBuild& with);

}  // namespace delta
