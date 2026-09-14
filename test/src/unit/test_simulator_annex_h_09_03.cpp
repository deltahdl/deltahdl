#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/dpi_context.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

TEST(DpiRuntime, SetAndGetScope) {
  DpiRuntime rt;
  DpiScope scope;
  scope.name = "top.mod";
  rt.PushScope(scope);

  const DpiScope* saved = rt.GetScope();
  ASSERT_NE(saved, nullptr);

  rt.PopScope();
  EXPECT_EQ(rt.CurrentScope(), nullptr);

  rt.SetScope(saved);
  EXPECT_EQ(rt.GetScope(), saved);
}

// §H.9.3: every svSetScope call reports the scope that was active immediately
// before it, and svGetScope keeps returning the most recently installed scope.
// Walking several context transitions confirms the previous-scope handoff holds
// across a chain rather than only for a single swap.
TEST(SvDpi, ScopeSetReturnsImmediatelyPriorScopeAcrossChain) {
  svScope original = svGetScope();
  int a = 1, b = 2, c = 3;
  auto scope_a = reinterpret_cast<svScope>(&a);
  auto scope_b = reinterpret_cast<svScope>(&b);
  auto scope_c = reinterpret_cast<svScope>(&c);

  EXPECT_EQ(svSetScope(scope_a), original);
  EXPECT_EQ(svGetScope(), scope_a);
  EXPECT_EQ(svSetScope(scope_b), scope_a);
  EXPECT_EQ(svGetScope(), scope_b);
  EXPECT_EQ(svSetScope(scope_c), scope_b);
  EXPECT_EQ(svGetScope(), scope_c);

  svSetScope(original);
}

// §H.9.3 edge case: installing a null scope clears the active scope while still
// reporting the prior non-null scope, exercising the swap with the boundary
// sentinel value.
TEST(SvDpi, ScopeSetToNullClearsActiveScopeAndReturnsPrior) {
  svScope original = svGetScope();
  int dummy = 7;
  auto scope = reinterpret_cast<svScope>(&dummy);

  svSetScope(scope);
  ASSERT_EQ(svGetScope(), scope);

  EXPECT_EQ(svSetScope(nullptr), scope);
  EXPECT_EQ(svGetScope(), nullptr);

  svSetScope(original);
}

// §H.9.3: a pointer stored under a (scope, key) pair is returned by a later
// svGetUserData with the same scope and key.
TEST(SvDpi, UserDataStoreRoundTrip) {
  int scope_obj = 0;
  int key_obj = 0;
  int payload = 99;
  auto scope = reinterpret_cast<svScope>(&scope_obj);

  EXPECT_EQ(svPutUserData(scope, &key_obj, &payload), 0);
  EXPECT_EQ(svGetUserData(scope, &key_obj), &payload);
}

// §H.9.3: the key together with the scope identifies an entry, so different
// keys (and different scopes) address independent storage.
TEST(SvDpi, UserDataKeyedByScopeAndKey) {
  int scope_a = 0;
  int scope_b = 0;
  int key1 = 0;
  int key2 = 0;
  int data1 = 1;
  int data2 = 2;
  int data3 = 3;
  auto sa = reinterpret_cast<svScope>(&scope_a);
  auto sb = reinterpret_cast<svScope>(&scope_b);

  ASSERT_EQ(svPutUserData(sa, &key1, &data1), 0);
  ASSERT_EQ(svPutUserData(sa, &key2, &data2), 0);
  ASSERT_EQ(svPutUserData(sb, &key1, &data3), 0);

  EXPECT_EQ(svGetUserData(sa, &key1), &data1);
  EXPECT_EQ(svGetUserData(sa, &key2), &data2);
  EXPECT_EQ(svGetUserData(sb, &key1), &data3);
}

// §H.9.3: a lookup for a (scope, key) that was never stored returns null.
TEST(SvDpi, UserDataReturnsNullWhenNeverStored) {
  int scope_obj = 0;
  int key_obj = 0;
  auto scope = reinterpret_cast<svScope>(&scope_obj);

  EXPECT_EQ(svGetUserData(scope, &key_obj), nullptr);
}

// §H.9.3 error cases: a null scope or null payload makes svPutUserData fail
// with -1 and stores nothing; svGetUserData with a null scope returns null.
TEST(SvDpi, UserDataRejectsNullScopeOrPayload) {
  int scope_obj = 0;
  int key_obj = 0;
  int payload = 5;
  auto scope = reinterpret_cast<svScope>(&scope_obj);

  EXPECT_EQ(svPutUserData(nullptr, &key_obj, &payload), -1);
  EXPECT_EQ(svPutUserData(scope, &key_obj, nullptr), -1);
  EXPECT_EQ(svGetUserData(nullptr, &key_obj), nullptr);

  // The rejected put left no entry behind.
  EXPECT_EQ(svGetUserData(scope, &key_obj), nullptr);
}

// §H.9.3: svGetScopeFromName shall return NULL for a name that is not a
// recognized instance scope, and a null query is likewise NULL.
TEST(SvDpi, GetScopeFromNameUnrecognizedIsNull) {
  EXPECT_EQ(svGetScopeFromName("top.no_such_scope_h_09_03"), nullptr);
  EXPECT_EQ(svGetScopeFromName(nullptr), nullptr);
}

// §H.9.3: once a fully qualified instance-scope name is recognized,
// svGetScopeFromName hands back its handle and svGetNameFromScope reverses that
// handle to the same fully qualified name.
TEST(SvDpi, ScopeNameAndHandleRoundTrip) {
  const char* name = "top.dut_h_09_03.u_alu";
  const DpiScope* registered = DpiRegisterScope(name);
  ASSERT_NE(registered, nullptr);

  svScope handle = svGetScopeFromName(name);
  EXPECT_EQ(handle, static_cast<svScope>(const_cast<DpiScope*>(registered)));
  ASSERT_NE(handle, nullptr);

  EXPECT_STREQ(svGetNameFromScope(handle), name);

  // Registering the same name again is idempotent: the same recognized handle
  // comes back, so the name resolves deterministically.
  EXPECT_EQ(svGetScopeFromName(name), handle);
}

// §H.9.3: an unrecognized handle (one this simulator never produced) and a null
// handle map to an empty name rather than an out-of-bounds dereference.
TEST(SvDpi, GetNameFromUnrecognizedScopeIsEmpty) {
  int stray = 0;
  EXPECT_STREQ(svGetNameFromScope(reinterpret_cast<svScope>(&stray)), "");
  EXPECT_STREQ(svGetNameFromScope(nullptr), "");
}

// §H.9.3: whether caller file/line is available is implementation-specific.
// When it is unavailable this simulator returns FALSE (0) and leaves the
// caller's fileName and lineNumber untouched.
TEST(SvDpi, GetCallerInfoUnavailableReturnsFalseAndLeavesArgsUnmodified) {
  const char* file = reinterpret_cast<const char*>(0xDEADBEEF);
  int line = 12345;

  EXPECT_EQ(svGetCallerInfo(&file, &line), 0);

  // FALSE result: the out-parameters are not modified.
  EXPECT_EQ(file, reinterpret_cast<const char*>(0xDEADBEEF));
  EXPECT_EQ(line, 12345);
}

// ---------------------------------------------------------------------------
// The clause's prose beside its function comments.
// ---------------------------------------------------------------------------

// §H.9.3: the terms scope and context are equivalent for DPI tasks and
// functions.
TEST(DpiContextUtilities, ScopeAndContextAreOneTerm) {
  EXPECT_TRUE(DpiScopeAndContextAreEquivalent());
}

// Installs `rt` as the registry the C layer reaches for the length of a case
// and takes it back out afterwards, the installation being process-wide.
struct ForeignRuntimeInstalled {
  explicit ForeignRuntimeInstalled(DpiRuntime* rt) { DpiSetForeignRuntime(rt); }
  ~ForeignRuntimeInstalled() { DpiSetForeignRuntime(nullptr); }
};

// §H.9.3: unless a prior svSetScope call occurred, svGetScope retrieves the
// scope of the executing import's declaration site, not its call site; after
// one it retrieves the scope that call set, and the call reported the scope
// active before it.
TEST(DpiContextUtilities, GetScopeIsTheDeclarationSiteUntilSetScopeMovesIt) {
  DpiRuntime rt;
  ForeignRuntimeInstalled installed(&rt);
  DpiScope decl_scope;
  decl_scope.name = "top.i1_m";
  rt.EnterContextImportCall("f", decl_scope);

  const auto* at_entry = static_cast<const DpiScope*>(svGetScope());
  ASSERT_NE(at_entry, nullptr);
  EXPECT_EQ(at_entry->name, "top.i1_m");

  const DpiScope* named = DpiRegisterScope("top.i2_m_h_09_03");
  EXPECT_EQ(svSetScope(const_cast<DpiScope*>(named)),
            static_cast<svScope>(const_cast<DpiScope*>(at_entry)));
  EXPECT_EQ(svGetScope(), static_cast<svScope>(const_cast<DpiScope*>(named)));
  rt.LeaveImportCall();
}

// §H.9.3: the behavior of the scope utilities is undefined for an entity that
// is not a member of a DPI context call chain, and that of an export for a
// member of a chain lacking the context characteristic; a member of a context
// chain has both defined. The runtime tells the two chains apart.
TEST(DpiContextUtilities, BehaviorIsDefinedForAMemberOfAContextChainAlone) {
  DpiRuntime rt;
  EXPECT_FALSE(DpiBehaviorIsDefinedForChainMember(rt.InContextCallChain()));

  rt.EnterNoncontextImportCall("plain");
  EXPECT_FALSE(DpiBehaviorIsDefinedForChainMember(rt.InContextCallChain()));
  rt.LeaveImportCall();

  DpiScope decl_scope;
  decl_scope.name = "top.i1_m";
  rt.EnterContextImportCall("ctx", decl_scope);
  EXPECT_TRUE(DpiBehaviorIsDefinedForChainMember(rt.InContextCallChain()));
  rt.LeaveImportCall();
}

// §H.9.3: shared or unique user data storage is controllable by the key: a
// related set of context imports using one key share, and a unique key gives
// unique storage. The address of a static C symbol is the suggested origin
// of a key, an arbitrary integer an unsafe one.
TEST(DpiContextUtilities, TheUserKeyControlsSharedOrUniqueStorage) {
  EXPECT_EQ(DpiUserDataStorageOf(true), DpiUserDataStorage::kShared);
  EXPECT_EQ(DpiUserDataStorageOf(false), DpiUserDataStorage::kUnique);
  EXPECT_TRUE(
      DpiUserKeyGenerationIsSafe(DpiUserKeyOrigin::kAddressOfStaticCSymbol));
  EXPECT_FALSE(DpiUserKeyGenerationIsSafe(DpiUserKeyOrigin::kArbitraryInteger));
}

// §H.9.3: a module m declaring a context import f and instantiated twice has
// f execute under two svScope values, and the two executing instances cannot
// share user data through svPutUserData's storage: what one instance stores
// under a key the other does not retrieve under the same key.
TEST(DpiContextUtilities, InstancesOfOneModuleShareNoUserData) {
  EXPECT_FALSE(DpiUserDataStorageIsSharedAcrossContexts());
  svScope i1 = const_cast<DpiScope*>(DpiRegisterScope("top.i1_m_h_09_03"));
  svScope i2 = const_cast<DpiScope*>(DpiRegisterScope("top.i2_m_h_09_03"));
  ASSERT_NE(i1, i2);
  static int key = 0;
  int data_of_i1 = 1;
  ASSERT_EQ(svPutUserData(i1, &key, &data_of_i1), 0);
  EXPECT_EQ(svGetUserData(i1, &key), &data_of_i1);
  EXPECT_EQ(svGetUserData(i2, &key), nullptr);
}

// §H.9.3: a user sharing a data area across contexts allocates the common
// area and stores its pointer for each context individually -- one
// svPutUserData call per context under the common key -- after which each
// context retrieves the same area.
TEST(DpiContextUtilities, ACommonAreaIsSharedByStoringItsPointerPerContext) {
  svScope i1 = const_cast<DpiScope*>(DpiRegisterScope("top.i1_n_h_09_03"));
  svScope i2 = const_cast<DpiScope*>(DpiRegisterScope("top.i2_n_h_09_03"));
  static int key = 0;
  int common_area = 42;
  EXPECT_EQ(DpiPutUserDataCallsSharingAnAreaAcross(2), 2u);
  ASSERT_EQ(svPutUserData(i1, &key, &common_area), 0);
  ASSERT_EQ(svPutUserData(i2, &key, &common_area), 0);
  EXPECT_EQ(svGetUserData(i1, &key), &common_area);
  EXPECT_EQ(svGetUserData(i2, &key), &common_area);
}

// §H.9.3: svSetScope shall be called before calling an export function unless
// the export is called while executing an import, which hands it the
// surrounding import's scope as the default scope.
TEST(DpiContextUtilities, SetScopeIsRequiredBeforeAnExportCallOutsideAnImport) {
  EXPECT_TRUE(DpiSvSetScopeIsRequiredBeforeExportCall(false));
  EXPECT_FALSE(DpiSvSetScopeIsRequiredBeforeExportCall(true));
}

// §H.9.3: the scope svGetScopeFromName retrieves can be a module, program,
// interface or generate scope; a package and the compilation unit have no
// instance-scope handle.
TEST(DpiContextUtilities, InstanceScopeHandlesNameFourKindsOfScope) {
  EXPECT_TRUE(
      DpiDeclarativeScopeHasInstanceScopeHandle(DpiDeclarativeScope::kModule));
  EXPECT_TRUE(
      DpiDeclarativeScopeHasInstanceScopeHandle(DpiDeclarativeScope::kProgram));
  EXPECT_TRUE(DpiDeclarativeScopeHasInstanceScopeHandle(
      DpiDeclarativeScope::kInterface));
  EXPECT_TRUE(DpiDeclarativeScopeHasInstanceScopeHandle(
      DpiDeclarativeScope::kGenerate));
  EXPECT_FALSE(
      DpiDeclarativeScopeHasInstanceScopeHandle(DpiDeclarativeScope::kPackage));
  EXPECT_FALSE(DpiDeclarativeScopeHasInstanceScopeHandle(
      DpiDeclarativeScope::kCompilationUnit));
}

// §H.9.3: a user data value of 0 is indiscernible from the NULL every error
// of svGetUserData returns, so its use is not suggested; any other pointer
// is told apart from an error.
TEST(DpiContextUtilities, AZeroUserDataValueIsIndiscernibleFromAnError) {
  int payload = 0;
  EXPECT_TRUE(DpiUserDataIsDiscernibleFromError(&payload));
  EXPECT_FALSE(DpiUserDataIsDiscernibleFromError(nullptr));
  svScope scope = const_cast<DpiScope*>(DpiRegisterScope("top.z_h_09_03"));
  static int key = 0;
  EXPECT_EQ(svPutUserData(scope, &key, nullptr), -1);
  EXPECT_EQ(svGetUserData(scope, &key), nullptr);
}

// §H.9.3: the file name svGetCallerInfo provides is owned by the
// SystemVerilog implementation and valid only until the next call to any
// SystemVerilog function; an application shall not modify or free it.
TEST(DpiContextUtilities,
     TheCallerInfoStringIsTheImplementationsUntilNextCall) {
  EXPECT_TRUE(DpiCallerInfoFileNameIsValid(false));
  EXPECT_FALSE(DpiCallerInfoFileNameIsValid(true));
  EXPECT_FALSE(DpiApplicationMayModifyOrFreeCallerInfoFileName());
}

}  // namespace
