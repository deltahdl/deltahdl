// §H.9.1: the two meanings of "context" for the subroutines of the DPI and of
// the VPI. A DPI imported task or function is a proxy for a native
// SystemVerilog one and follows its model: a native subroutine operates in the
// scope of its declaration, so a function f() declared in a module m
// instantiated as top.i1_m executes in that instance, with unqualified
// visibility only for the variables local to it, however distant the code
// that calls it through a hierarchical reference is; an import likewise
// executes in the context of the declarative scope surrounding its
// declaration rather than that of its call sites. That is DPI context. A VPI
// function instead executes in a context associated with its call site, its C
// code retrieving a context handle for the call site of the system task and
// gleaning arguments and items of the call site's surrounding scope through
// it. That is VPI context.
//
// The SystemVerilog context of an export needs to be known when the export is
// called, from an import included. It is the scope an import named with
// svSetScope before calling, and otherwise the instantiated scope where the
// import's declaration is located; since imports in diverse instantiated
// scopes can export the same subroutine, one export exists as several
// instances after elaboration, with different contexts until svSetScope names
// one, each reflecting its imported caller's instantiated scope.
//
// DpiRuntime carries the mechanics -- the scope an export call runs under and
// the instance it reaches. This header states the clause's model beside it.
#ifndef DELTA_SIMULATOR_DPI_CONTEXT_H_
#define DELTA_SIMULATOR_DPI_CONTEXT_H_

#include <array>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

namespace delta {

// §H.9.1: the two categories of subroutine that need to understand their
// context, and the native subroutine an import is a proxy for.
enum class DpiContextUser : uint8_t {
  kNativeSystemVerilogSubroutine,
  kDpiImportedSubroutine,
  kVpiFunction,
};

// §H.9.1: the two meanings the term context has, one per category.
enum class DpiContextNotion : uint8_t {
  kDpiContext,
  kVpiContext,
};

// §H.9.1: what a context is associated with: the declaration site, whose
// surrounding declarative scope the subroutine executes in, or the call site.
enum class DpiContextSite : uint8_t {
  kDeclarationSite,
  kCallSite,
};

// §H.9.1: the notion of context a category of subroutine has. A native
// subroutine and the import that is a proxy for it have DPI context; a VPI
// function has VPI context.
DpiContextNotion DpiContextNotionOf(DpiContextUser user);

// §H.9.1: the site a notion of context is associated with. DPI context is the
// declaration site's; VPI context is the call site's.
DpiContextSite DpiContextSiteOf(DpiContextNotion notion);

// §H.9.1: the context a native or imported subroutine executes in, given the
// instantiated scope of its declaration and the scope of the code calling it:
// the declaration's, whatever the call site's.
std::string_view DpiContextOfSubroutine(std::string_view declaration_scope,
                                        std::string_view call_site_scope);

// §H.9.1: whether a subroutine executing in the context `context` has
// unqualified visibility of a variable local to the scope `variable_scope`.
// It has it only for the variables local to its own instance, and not for
// those in the calling code's scope.
bool DpiHasUnqualifiedVisibility(std::string_view context,
                                 std::string_view variable_scope);

// §H.9.1: where the context of an export called from an import comes from:
// set explicitly by an svSetScope the import invoked before calling, or,
// without one, the instantiated scope where the import declaration is
// located.
enum class DpiExportContextOrigin : uint8_t {
  kSetExplicitlyBySvSetScope,
  kImportDeclarationsInstantiatedScope,
};

DpiExportContextOrigin DpiExportContextOriginOf(bool sv_set_scope_invoked);

// §H.9.1: the context an export called from an import runs under: the scope
// svSetScope named where the import invoked it, else the instantiated scope
// of the import's declaration.
std::string_view DpiContextOfExportCalledFromImport(
    std::string_view import_declaration_scope,
    std::optional<std::string_view> sv_set_scope_named);

// §H.9.1: how many instances of one export exist after elaboration when the
// imports exporting it are declared in the given instantiated scopes -- one
// per distinct scope, each instance's context reflecting its imported
// caller's instantiated scope until svSetScope is invoked.
uint32_t DpiExportInstanceCount(
    const std::vector<std::string_view>& importing_scopes);

// §H.9.2: the declarative scopes a DPI imported or exported task or function
// can be declared in, in the clause's order.
enum class DpiDeclarativeScope : uint8_t {
  kModule,
  kProgram,
  kInterface,
  kPackage,
  kCompilationUnit,
  kGenerate,
};

std::array<DpiDeclarativeScope, 6> DpiDeclarativeScopes();

// §H.9.2: the context of an imported or exported subroutine corresponds to
// the fully qualified name of the subroutine minus the subroutine name
// itself: top.i1_m.f has the context top.i1_m, and pkg::f the context pkg. A
// name with no qualification is the compilation unit's, whose context is
// empty.
std::string_view DpiContextOfQualifiedName(std::string_view qualified_name);

// §H.9.2: the context property is transitive through imported and exported
// context subroutines declared in one scope, so an import running in a
// context can call an export available in that same context without any use
// of svSetScope. An export in another context is reached through svSetScope
// (§35.5.3).
bool DpiExportIsCallableWithoutSvSetScope(std::string_view import_context,
                                          std::string_view export_context);

// §H.9.2: the ways control passes across the boundary between SystemVerilog
// and a DPI import call chain with the context property.
enum class DpiBoundaryCrossing : uint8_t {
  // A call of an export from the chain, and the export's return.
  kExportCallAndReturn,
  // C code unwinding across the boundary by setjmp and longjmp, circumventing
  // the SystemVerilog exports it passes.
  kUnwindingBySetjmpAndLongjmp,
};

// §H.9.2: whether user code's behavior is defined for a crossing. Across a
// call and return the import's context is potentially set or reset by the
// rules of §35.5.3; for C code that unwinds across the boundary it is
// undefined.
bool DpiBehaviorIsDefinedAcross(DpiBoundaryCrossing crossing);

// §H.9.2: whether the value of the import's context is potentially set or
// reset when control passes across the boundary: it is where the chain has
// the context property, and a chain without it has no context to change.
bool DpiImportContextMayChangeAcrossBoundary(bool chain_has_context_property);

}  // namespace delta

#endif  // DELTA_SIMULATOR_DPI_CONTEXT_H_
