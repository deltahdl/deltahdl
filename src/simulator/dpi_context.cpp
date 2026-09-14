#include "simulator/dpi_context.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

namespace delta {

DpiContextNotion DpiContextNotionOf(DpiContextUser user) {
  // §H.9.1: an import is a proxy for a native subroutine and follows the same
  // model, so both have DPI context; only a VPI function has VPI context.
  return user == DpiContextUser::kVpiFunction ? DpiContextNotion::kVpiContext
                                              : DpiContextNotion::kDpiContext;
}

DpiContextSite DpiContextSiteOf(DpiContextNotion notion) {
  return notion == DpiContextNotion::kVpiContext
             ? DpiContextSite::kCallSite
             : DpiContextSite::kDeclarationSite;
}

std::string_view DpiContextOfSubroutine(std::string_view declaration_scope,
                                        std::string_view /*call_site_scope*/) {
  // §H.9.1: a native or imported subroutine executes in the context of its
  // surrounding declarative scope rather than that of its call site.
  return declaration_scope;
}

bool DpiHasUnqualifiedVisibility(std::string_view context,
                                 std::string_view variable_scope) {
  return context == variable_scope;
}

DpiExportContextOrigin DpiExportContextOriginOf(bool sv_set_scope_invoked) {
  return sv_set_scope_invoked
             ? DpiExportContextOrigin::kSetExplicitlyBySvSetScope
             : DpiExportContextOrigin::kImportDeclarationsInstantiatedScope;
}

std::string_view DpiContextOfExportCalledFromImport(
    std::string_view import_declaration_scope,
    std::optional<std::string_view> sv_set_scope_named) {
  return sv_set_scope_named.value_or(import_declaration_scope);
}

uint32_t DpiExportInstanceCount(
    const std::vector<std::string_view>& importing_scopes) {
  // §H.9.1: one instance per instantiated scope; two imports declared in one
  // scope share the instance that scope's context reflects.
  std::vector<std::string_view> distinct(importing_scopes);
  std::sort(distinct.begin(), distinct.end());
  distinct.erase(std::unique(distinct.begin(), distinct.end()), distinct.end());
  return static_cast<uint32_t>(distinct.size());
}

std::array<DpiDeclarativeScope, 6> DpiDeclarativeScopes() {
  return {
      DpiDeclarativeScope::kModule,          DpiDeclarativeScope::kProgram,
      DpiDeclarativeScope::kInterface,       DpiDeclarativeScope::kPackage,
      DpiDeclarativeScope::kCompilationUnit, DpiDeclarativeScope::kGenerate};
}

std::string_view DpiContextOfQualifiedName(std::string_view qualified_name) {
  // §H.9.2: minus the subroutine name itself, which follows the last of the
  // hierarchical dot and the package's scope resolution operator.
  const size_t kDot = qualified_name.rfind('.');
  const size_t kColons = qualified_name.rfind("::");
  if (kDot == std::string_view::npos && kColons == std::string_view::npos) {
    return {};
  }
  if (kColons != std::string_view::npos &&
      (kDot == std::string_view::npos || kColons > kDot)) {
    return qualified_name.substr(0, kColons);
  }
  return qualified_name.substr(0, kDot);
}

bool DpiExportIsCallableWithoutSvSetScope(std::string_view import_context,
                                          std::string_view export_context) {
  return import_context == export_context;
}

bool DpiBehaviorIsDefinedAcross(DpiBoundaryCrossing crossing) {
  return crossing == DpiBoundaryCrossing::kExportCallAndReturn;
}

bool DpiImportContextMayChangeAcrossBoundary(bool chain_has_context_property) {
  return chain_has_context_property;
}

bool DpiScopeAndContextAreEquivalent() { return true; }

bool DpiBehaviorIsDefinedForChainMember(bool chain_is_context) {
  return chain_is_context;
}

DpiUserDataStorage DpiUserDataStorageOf(bool related_imports_use_one_key) {
  return related_imports_use_one_key ? DpiUserDataStorage::kShared
                                     : DpiUserDataStorage::kUnique;
}

bool DpiUserKeyGenerationIsSafe(DpiUserKeyOrigin origin) {
  return origin == DpiUserKeyOrigin::kAddressOfStaticCSymbol;
}

bool DpiUserDataStorageIsSharedAcrossContexts() { return false; }

uint32_t DpiPutUserDataCallsSharingAnAreaAcross(uint32_t context_count) {
  // §H.9.3: one call per context, the pointer being stored individually for
  // each of the contexts in question.
  return context_count;
}

bool DpiSvSetScopeIsRequiredBeforeExportCall(
    bool export_called_while_executing_import) {
  return !export_called_while_executing_import;
}

bool DpiDeclarativeScopeHasInstanceScopeHandle(DpiDeclarativeScope scope) {
  return scope != DpiDeclarativeScope::kPackage &&
         scope != DpiDeclarativeScope::kCompilationUnit;
}

bool DpiUserDataIsDiscernibleFromError(const void* user_data) {
  return user_data != nullptr;
}

bool DpiCallerInfoFileNameIsValid(bool sv_function_called_since) {
  return !sv_function_called_since;
}

bool DpiApplicationMayModifyOrFreeCallerInfoFileName() { return false; }

}  // namespace delta
