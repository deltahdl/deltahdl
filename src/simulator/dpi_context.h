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

// §H.9.3: the terms scope and context are equivalent for DPI tasks and
// functions, scope being the one the subroutine names use for consistency
// with the rest of SystemVerilog.
bool DpiScopeAndContextAreEquivalent();

// §H.9.3: the behavior of the functions that retrieve and manipulate the
// current operational scope is undefined when they are invoked by an entity
// other than a member of a DPI context call chain, and that of an exported
// subroutine is undefined when it is invoked by a member of a chain that
// lacks the context characteristic. Both are defined for a member of a
// context chain, which DpiRuntime::InContextCallChain answers for the
// current point of execution.
bool DpiBehaviorIsDefinedForChainMember(bool chain_is_context);

// §H.9.3: the "put" and "get" user data functions set data specific to C
// models into the simulator for later retrieval, shared or unique per
// function under the control of a user-defined key: a related set of context
// imports using one key share their storage, and an import using a key of
// its own has unique storage.
enum class DpiUserDataStorage : uint8_t { kShared, kUnique };

DpiUserDataStorage DpiUserDataStorageOf(bool related_imports_use_one_key);

// §H.9.3: a unique key has to be unique from every key any C code in the
// simulation could use, completely unknown C code included, so taking the
// address of a static C symbol -- a function or an object of static
// storage -- is what is suggested for generating one; generating keys from
// arbitrary integers is not a safe practice.
enum class DpiUserKeyOrigin : uint8_t {
  kAddressOfStaticCSymbol,
  kArbitraryInteger,
};

bool DpiUserKeyGenerationIsSafe(DpiUserKeyOrigin origin);

// §H.9.3: it is never possible to share user data storage across different
// contexts: a module declaring a context import and instantiated more than
// once has the import execute under a different svScope per instance, and no
// two of those executing instances can share user data through the storage
// svPutUserData provides. A user sharing a data area across contexts
// allocates the common area and stores its pointer for each context in
// question with one svPutUserData call per context, a common key
// notwithstanding, because the data is associated with the individual
// scopes.
bool DpiUserDataStorageIsSharedAcrossContexts();
uint32_t DpiPutUserDataCallsSharingAnAreaAcross(uint32_t context_count);

// §H.9.3: svSetScope shall be called before calling an export function,
// unless the export is called while executing an import, in which case the
// export inherits the scope of the surrounding import, known as the "default
// scope".
bool DpiSvSetScopeIsRequiredBeforeExportCall(
    bool export_called_while_executing_import);

// §H.9.3: svGetScopeFromName retrieves the svScope of the instance scope of
// an arbitrary function declaration, which can be a module, program,
// interface or generate scope. A package and the compilation unit, the other
// two scopes §H.9.2 lets a subroutine be declared in, are not instance
// scopes with such a handle.
bool DpiDeclarativeScopeHasInstanceScopeHandle(DpiDeclarativeScope scope);

// §H.9.3: svGetUserData returns NULL for every error case and where no prior
// svPutUserData stored a pointer, so a user data value of 0 is indiscernible
// from an error status when retrieved, and its use is not suggested.
bool DpiUserDataIsDiscernibleFromError(const void* user_data);

// §H.9.3: the file name svGetCallerInfo provides is a string owned by the
// SystemVerilog implementation, valid only until the next call to any
// SystemVerilog function, which an application shall neither modify nor
// free.
bool DpiCallerInfoFileNameIsValid(bool sv_function_called_since);
bool DpiApplicationMayModifyOrFreeCallerInfoFileName();

}  // namespace delta

#endif  // DELTA_SIMULATOR_DPI_CONTEXT_H_
