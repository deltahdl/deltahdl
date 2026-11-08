#include <gtest/gtest.h>

#include <string>

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

TEST(SvDpi, UserDataStoreRoundTrip) {
  static int key_obj = 0;
  int payload = 99;
  svScope scope =
      const_cast<DpiScope*>(DpiRegisterScope("top.round_trip_h_09_03"));

  EXPECT_EQ(svPutUserData(scope, &key_obj, &payload), 0);
  EXPECT_EQ(svGetUserData(scope, &key_obj), &payload);
}

TEST(SvDpi, UserDataKeyedByScopeAndKey) {
  static int key1 = 0;
  static int key2 = 0;
  int data1 = 1;
  int data2 = 2;
  int data3 = 3;
  svScope sa = const_cast<DpiScope*>(DpiRegisterScope("top.keyed_a_h_09_03"));
  svScope sb = const_cast<DpiScope*>(DpiRegisterScope("top.keyed_b_h_09_03"));

  ASSERT_EQ(svPutUserData(sa, &key1, &data1), 0);
  ASSERT_EQ(svPutUserData(sa, &key2, &data2), 0);
  ASSERT_EQ(svPutUserData(sb, &key1, &data3), 0);

  EXPECT_EQ(svGetUserData(sa, &key1), &data1);
  EXPECT_EQ(svGetUserData(sa, &key2), &data2);
  EXPECT_EQ(svGetUserData(sb, &key1), &data3);
}

TEST(SvDpi, UserDataReturnsNullWhenNeverStored) {
  static int key_obj = 0;
  svScope scope =
      const_cast<DpiScope*>(DpiRegisterScope("top.never_stored_h_09_03"));

  EXPECT_EQ(svGetUserData(scope, &key_obj), nullptr);
}

TEST(SvDpi, UserDataRejectsNullScopeOrPayload) {
  static int key_obj = 0;
  int payload = 5;
  svScope scope =
      const_cast<DpiScope*>(DpiRegisterScope("top.rejects_null_h_09_03"));

  EXPECT_EQ(svPutUserData(nullptr, &key_obj, &payload), -1);
  EXPECT_EQ(svPutUserData(scope, &key_obj, nullptr), -1);
  EXPECT_EQ(svGetUserData(nullptr, &key_obj), nullptr);

  EXPECT_EQ(svGetUserData(scope, &key_obj), nullptr);
}

TEST(SvDpi, UserDataRejectsAHandleThatNamesNoScope) {
  static int not_a_scope = 0;
  static int key_obj = 0;
  int payload = 7;
  int peer_payload = 8;
  auto invalid = reinterpret_cast<svScope>(&not_a_scope);
  svScope peer =
      const_cast<DpiScope*>(DpiRegisterScope("top.invalid_peer_h_09_03"));

  ASSERT_EQ(svPutUserData(peer, &key_obj, &peer_payload), 0);
  EXPECT_EQ(svPutUserData(invalid, &key_obj, &payload), -1);
  EXPECT_EQ(svGetUserData(invalid, &key_obj), nullptr);
  EXPECT_EQ(svGetUserData(peer, &key_obj), &peer_payload);
}

TEST(SvDpi, UserDataAcceptsTheUnnamedScopeOfTheCurrentFrame) {
  static int not_a_scope = 0;
  static int key_obj = 0;
  int payload = 11;
  DpiRuntime* installed = DpiForeignRuntime();
  DpiRuntime rt;
  DpiSetForeignRuntime(&rt);
  rt.PushScope(DpiScope{});
  svScope scope = svGetScope();

  EXPECT_EQ(svPutUserData(scope, &key_obj, &payload), 0);
  EXPECT_EQ(svGetUserData(scope, &key_obj), &payload);
  EXPECT_EQ(svPutUserData(reinterpret_cast<svScope>(&not_a_scope), &key_obj,
                          &payload),
            -1);

  rt.PopScope();
  DpiSetForeignRuntime(installed);
}

TEST(SvDpi, GetScopeFromNameUnrecognizedIsNull) {
  EXPECT_EQ(svGetScopeFromName("top.no_such_scope_h_09_03"), nullptr);
  EXPECT_EQ(svGetScopeFromName(nullptr), nullptr);
}

TEST(SvDpi, ScopeNameAndHandleRoundTrip) {
  const char* name = "top.dut_h_09_03.u_alu";
  const DpiScope* registered = DpiRegisterScope(name);
  ASSERT_NE(registered, nullptr);

  svScope handle = svGetScopeFromName(name);
  EXPECT_EQ(handle, static_cast<svScope>(const_cast<DpiScope*>(registered)));
  ASSERT_NE(handle, nullptr);

  EXPECT_STREQ(svGetNameFromScope(handle), name);

  EXPECT_EQ(svGetScopeFromName(name), handle);
}

TEST(SvDpi, GetNameFromUnrecognizedScopeIsEmpty) {
  int stray = 0;
  EXPECT_STREQ(svGetNameFromScope(reinterpret_cast<svScope>(&stray)), "");
  EXPECT_STREQ(svGetNameFromScope(nullptr), "");
}

TEST(SvDpi, GetCallerInfoUnavailableReturnsFalseAndLeavesArgsUnmodified) {
  const char* file = reinterpret_cast<const char*>(0xDEADBEEF);
  int line = 12345;

  EXPECT_EQ(svGetCallerInfo(&file, &line), 0);

  EXPECT_EQ(file, reinterpret_cast<const char*>(0xDEADBEEF));
  EXPECT_EQ(line, 12345);
}

TEST(DpiContextUtilities, ScopeAndContextAreOneTerm) {
  EXPECT_TRUE(DpiScopeAndContextAreEquivalent());
}

struct ForeignRuntimeInstalled {
  explicit ForeignRuntimeInstalled(DpiRuntime* rt) { DpiSetForeignRuntime(rt); }
  ~ForeignRuntimeInstalled() { DpiSetForeignRuntime(nullptr); }
};

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

TEST(DpiContextUtilities, TheUserKeyControlsSharedOrUniqueStorage) {
  EXPECT_EQ(DpiUserDataStorageOf(true), DpiUserDataStorage::kShared);
  EXPECT_EQ(DpiUserDataStorageOf(false), DpiUserDataStorage::kUnique);
  EXPECT_TRUE(
      DpiUserKeyGenerationIsSafe(DpiUserKeyOrigin::kAddressOfStaticCSymbol));
  EXPECT_FALSE(DpiUserKeyGenerationIsSafe(DpiUserKeyOrigin::kArbitraryInteger));
}

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

TEST(DpiContextUtilities, SetScopeIsRequiredBeforeAnExportCallOutsideAnImport) {
  EXPECT_TRUE(DpiSvSetScopeIsRequiredBeforeExportCall(false));
  EXPECT_FALSE(DpiSvSetScopeIsRequiredBeforeExportCall(true));
}

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

TEST(DpiContextUtilities, AZeroUserDataValueIsIndiscernibleFromAnError) {
  int payload = 0;
  EXPECT_TRUE(DpiUserDataIsDiscernibleFromError(&payload));
  EXPECT_FALSE(DpiUserDataIsDiscernibleFromError(nullptr));
  svScope scope = const_cast<DpiScope*>(DpiRegisterScope("top.z_h_09_03"));
  static int key = 0;
  EXPECT_EQ(svPutUserData(scope, &key, nullptr), -1);
  EXPECT_EQ(svGetUserData(scope, &key), nullptr);
}

TEST(DpiContextUtilities,
     TheCallerInfoStringIsTheImplementationsUntilNextCall) {
  EXPECT_TRUE(DpiCallerInfoFileNameIsValid(false));
  EXPECT_FALSE(DpiCallerInfoFileNameIsValid(true));
  EXPECT_FALSE(DpiApplicationMayModifyOrFreeCallerInfoFileName());
}

}  // namespace
