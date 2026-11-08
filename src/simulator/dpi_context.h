#ifndef DELTA_SIMULATOR_DPI_CONTEXT_H_
#define DELTA_SIMULATOR_DPI_CONTEXT_H_

#include <array>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

namespace delta {

enum class DpiContextUser : uint8_t {
  kNativeSystemVerilogSubroutine,
  kDpiImportedSubroutine,
  kVpiFunction,
};

enum class DpiContextNotion : uint8_t {
  kDpiContext,
  kVpiContext,
};

enum class DpiContextSite : uint8_t {
  kDeclarationSite,
  kCallSite,
};

DpiContextNotion DpiContextNotionOf(DpiContextUser user);

DpiContextSite DpiContextSiteOf(DpiContextNotion notion);

std::string_view DpiContextOfSubroutine(std::string_view declaration_scope,
                                        std::string_view call_site_scope);

bool DpiHasUnqualifiedVisibility(std::string_view context,
                                 std::string_view variable_scope);

enum class DpiExportContextOrigin : uint8_t {
  kSetExplicitlyBySvSetScope,
  kImportDeclarationsInstantiatedScope,
};

DpiExportContextOrigin DpiExportContextOriginOf(bool sv_set_scope_invoked);

std::string_view DpiContextOfExportCalledFromImport(
    std::string_view import_declaration_scope,
    std::optional<std::string_view> sv_set_scope_named);

uint32_t DpiExportInstanceCount(
    const std::vector<std::string_view>& importing_scopes);

enum class DpiDeclarativeScope : uint8_t {
  kModule,
  kProgram,
  kInterface,
  kPackage,
  kCompilationUnit,
  kGenerate,
};

std::array<DpiDeclarativeScope, 6> DpiDeclarativeScopes();

std::string_view DpiContextOfQualifiedName(std::string_view qualified_name);

bool DpiExportIsCallableWithoutSvSetScope(std::string_view import_context,
                                          std::string_view export_context);

enum class DpiBoundaryCrossing : uint8_t {
  kExportCallAndReturn,
  kUnwindingBySetjmpAndLongjmp,
};

bool DpiBehaviorIsDefinedAcross(DpiBoundaryCrossing crossing);

bool DpiImportContextMayChangeAcrossBoundary(bool chain_has_context_property);

bool DpiScopeAndContextAreEquivalent();

bool DpiBehaviorIsDefinedForChainMember(bool chain_is_context);

enum class DpiUserDataStorage : uint8_t { kShared, kUnique };

DpiUserDataStorage DpiUserDataStorageOf(bool related_imports_use_one_key);

enum class DpiUserKeyOrigin : uint8_t {
  kAddressOfStaticCSymbol,
  kArbitraryInteger,
};

bool DpiUserKeyGenerationIsSafe(DpiUserKeyOrigin origin);

bool DpiUserDataStorageIsSharedAcrossContexts();
uint32_t DpiPutUserDataCallsSharingAnAreaAcross(uint32_t context_count);

bool DpiSvSetScopeIsRequiredBeforeExportCall(
    bool export_called_while_executing_import);

bool DpiDeclarativeScopeHasInstanceScopeHandle(DpiDeclarativeScope scope);

bool DpiUserDataIsDiscernibleFromError(const void* user_data);

bool DpiCallerInfoFileNameIsValid(bool sv_function_called_since);
bool DpiApplicationMayModifyOrFreeCallerInfoFileName();

bool DpiOpenArrayHandleIsInterchangeableWithVpiHandle();

std::array<std::string_view, 10> DpiVpiRoutinesCallableWithoutContext();
bool DpiVpiRoutineRequiresContext(std::string_view vpi_routine);

enum class DpiVpiActivity : uint8_t {
  kSystemTaskCallSiteHandle,
  kSystemTaskCallback,
  kIterateTopLevelModules,
};

bool DpiVpiActivityIsAvailableFromContextImport(DpiVpiActivity activity);

}  // namespace delta

#endif
