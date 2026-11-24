#include <gtest/gtest.h>

#include <array>
#include <cstring>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "helpers_dpi_scope_names.h"
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

int CheckOwnScope() {
  svScope scope = svGetScope();
  const char* name = svGetNameFromScope(scope);
  SeeInC({scope != nullptr && name != nullptr &&
          svGetScopeFromName(name) == scope});
  return SeeScopeName();
}

constexpr const char* kTwoInstancesSeeingTheirScope =
    "  import \"DPI-C\" context function int see_scope();\n"
    "  int r;\n"
    "  initial r = see_scope();\n"
    "endmodule\n";

TEST(ScopeInADesign, EachInstanceSeesItsOwnName) {
  std::string src = "module m;\n";
  src += kTwoInstancesSeeingTheirScope;
  src += "module own;\n  m i1();\n  m i2();\nendmodule\n";
  EXPECT_EQ(ScopeNamesOfRun(src, "annex_h_09_03_own_name"),
            (std::vector<std::string>{"own.i1", "own.i2"}));
}

std::vector<long long> NamesMapBack(const std::string& src) {
  SimFixture f;
  RunDesignWithC(src, f, {{"see_scope", CAddress(&CheckOwnScope)}},
                 "annex_h_09_03_map_back");
  return SeenInC();
}

TEST(ScopeInADesign, AModulesScopeMapsToItsNameAndBack) {
  std::string src = "module m;\n";
  src += kTwoInstancesSeeingTheirScope;
  src += "module mback;\n  m i1();\nendmodule\n";
  EXPECT_EQ(NamesMapBack(src), (std::vector<long long>{1}));
  EXPECT_EQ(ScopeNamesSeenInC(), (std::vector<std::string>{"mback.i1"}));
}

TEST(ScopeInADesign, AProgramsScopeMapsToItsNameAndBack) {
  EXPECT_EQ(NamesMapBack("program p;\n"
                         "  import \"DPI-C\" context function int "
                         "see_scope();\n"
                         "  int r;\n"
                         "  initial r = see_scope();\n"
                         "endprogram\n"
                         "module pback;\n"
                         "  p u();\n"
                         "endmodule\n"),
            (std::vector<long long>{1}));
  EXPECT_EQ(ScopeNamesSeenInC(), (std::vector<std::string>{"pback.u"}));
}

TEST(ScopeInADesign, AnInterfacesScopeMapsToItsNameAndBack) {
  EXPECT_EQ(NamesMapBack("interface i;\n"
                         "  import \"DPI-C\" context function int "
                         "see_scope();\n"
                         "  int r;\n"
                         "  initial r = see_scope();\n"
                         "endinterface\n"
                         "module iback;\n"
                         "  i u();\n"
                         "endmodule\n"),
            (std::vector<long long>{1}));
  EXPECT_EQ(ScopeNamesSeenInC(), (std::vector<std::string>{"iback.u"}));
}

TEST(ScopeInADesign, DISABLED_AGenerateBlocksScopeMapsToItsNameAndBack) {
  EXPECT_EQ(NamesMapBack("module gback;\n"
                         "  for (genvar i = 1; i < 2; i++) begin : g\n"
                         "    import \"DPI-C\" context function int "
                         "see_scope();\n"
                         "    int r;\n"
                         "    initial r = see_scope();\n"
                         "  end\n"
                         "endmodule\n"),
            (std::vector<long long>{1}));
  EXPECT_EQ(ScopeNamesSeenInC(), (std::vector<std::string>{"gback.g[1]"}));
}

int FindScopeByName(const char* path) {
  svScope scope = svGetScopeFromName(path);
  if (scope == nullptr) return 0;
  const char* name = svGetNameFromScope(scope);
  return name != nullptr && std::strcmp(name, path) == 0 ? 1 : -1;
}

int FoundInTheDesign(const std::string& before, const std::string& items,
                     const std::string& path) {
  SimFixture f;
  std::string src = before;
  src += "module t;\n";
  src += items;
  src += "  import \"DPI-C\" context function int find(input string path);\n";
  src += "  int r;\n  initial r = find(\"";
  src += path;
  src += "\");\nendmodule\n";
  RunDesignWithC(src, f, {{"find", CAddress(&FindScopeByName)}},
                 "annex_h_09_03_find");
  return static_cast<int>(DesignValue(f, "r"));
}

TEST(ScopeFromNameInADesign, AnExportingModuleInstanceIsFound) {
  EXPECT_EQ(FoundInTheDesign("module m;\n"
                             "  function int found_f(); return 1; endfunction\n"
                             "  export \"DPI-C\" function found_f;\n"
                             "endmodule\n",
                             "  m u_exp();\n", "t.u_exp"),
            1);
}

TEST(ScopeFromNameInADesign, DISABLED_AModuleInstanceWithoutAnExportIsFound) {
  EXPECT_EQ(FoundInTheDesign("module m;\n"
                             "  int v;\n"
                             "endmodule\n",
                             "  m u_plain();\n", "t.u_plain"),
            1);
}

TEST(ScopeFromNameInADesign, ATopModuleWithoutAnExportIsFound) {
  EXPECT_EQ(FoundInTheDesign("", "", "t"), 1);
}

TEST(ScopeFromNameInADesign, DISABLED_AProgramInstanceIsFound) {
  EXPECT_EQ(FoundInTheDesign("program p;\n"
                             "  int v;\n"
                             "endprogram\n",
                             "  p u_prog();\n", "t.u_prog"),
            1);
}

TEST(ScopeFromNameInADesign, DISABLED_AnInterfaceInstanceIsFound) {
  EXPECT_EQ(FoundInTheDesign("interface i;\n"
                             "  int v;\n"
                             "endinterface\n",
                             "  i u_if();\n", "t.u_if"),
            1);
}

TEST(ScopeFromNameInADesign, DISABLED_ALoopGenerateBlockIsFound) {
  EXPECT_EQ(FoundInTheDesign("",
                             "  for (genvar k = 0; k < 2; k++) begin : g\n"
                             "    int v;\n"
                             "  end\n",
                             "t.g[1]"),
            1);
}

TEST(ScopeFromNameInADesign, DISABLED_AConditionalGenerateBlockIsFound) {
  EXPECT_EQ(FoundInTheDesign("",
                             "  if (1) begin : g_if\n"
                             "    int v;\n"
                             "  end\n",
                             "t.g_if"),
            1);
}

TEST(ScopeFromNameInADesign, ANameOfNoScopeIsNotFound) {
  EXPECT_EQ(FoundInTheDesign("", "", "t.u_missing"), 0);
  EXPECT_EQ(FoundInTheDesign("",
                             "  if (0) begin : g_off\n"
                             "    int v;\n"
                             "  end\n",
                             "t.g_off"),
            0);
}

int MoveToTheOtherInstance() {
  svScope own = svGetScope();
  svScope other = svGetScopeFromName("moved.u2");
  svScope previous = svSetScope(other);
  auto g = NamedExport<int (*)()>("moved_g");
  SeeInC({other != nullptr, previous == own, svGetScope() == other,
          g == nullptr ? -1 : g(), svSetScope(own) == other,
          g == nullptr ? -1 : g(), svSetScope(other) == own});
  return 0;
}

TEST(ScopeInADesign, SetScopeRedirectsTheExportUntilItIsMovedBack) {
  SimFixture f;
  RunDesignWithC(
      "module m #(int ID);\n"
      "  int v = ID;\n"
      "  function int moved_g(); return v; endfunction\n"
      "  export \"DPI-C\" function moved_g;\n"
      "  import \"DPI-C\" context function int move();\n"
      "  import \"DPI-C\" context function int see_scope();\n"
      "  int r;\n"
      "  initial if (ID == 40) begin\n"
      "    #1 r = move();\n"
      "    r = see_scope();\n"
      "  end\n"
      "endmodule\n"
      "module moved;\n"
      "  m #(40) u1();\n"
      "  m #(80) u2();\n"
      "endmodule\n",
      f,
      {{"move", CAddress(&MoveToTheOtherInstance)},
       {"see_scope", CAddress(&SeeScopeName)}},
      "annex_h_09_03_set_scope");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{1, 1, 1, 80, 1, 40, 1}));
  EXPECT_EQ(ScopeNamesSeenInC(), (std::vector<std::string>{"moved.u1"}));
}

std::array<int, 4>& UserKeysAndData() {
  static std::array<int, 4> storage;
  return storage;
}

int StoreUnderTheSharedKey() {
  return svPutUserData(svGetScope(), &UserKeysAndData()[0],
                       &UserKeysAndData()[1]);
}

int FetchUnderTheSharedKey() {
  void* found = svGetUserData(svGetScope(), &UserKeysAndData()[0]);
  return found == nullptr ? 0 : found == &UserKeysAndData()[1] ? 1 : -1;
}

int FetchUnderItsOwnKey() {
  void* found = svGetUserData(svGetScope(), &UserKeysAndData()[2]);
  return found == nullptr ? 0 : 1;
}

TEST(UserDataInADesign, ImportsOfOneScopeShareTheDataOfOneKey) {
  SimFixture f;
  RunDesignWithC(
      "module shared_key;\n"
      "  import \"DPI-C\" context function int store();\n"
      "  import \"DPI-C\" context function int fetch();\n"
      "  import \"DPI-C\" context function int fetch_own();\n"
      "  int before_put, put, got, own;\n"
      "  initial begin\n"
      "    before_put = fetch();\n"
      "    put = store();\n"
      "    got = fetch();\n"
      "    own = fetch_own();\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"store", CAddress(&StoreUnderTheSharedKey)},
       {"fetch", CAddress(&FetchUnderTheSharedKey)},
       {"fetch_own", CAddress(&FetchUnderItsOwnKey)}},
      "annex_h_09_03_shared_key");
  EXPECT_EQ(DesignValue(f, "before_put"), 0u);
  EXPECT_EQ(DesignValue(f, "put"), 0u);
  EXPECT_EQ(DesignValue(f, "got"), 1u);
  EXPECT_EQ(DesignValue(f, "own"), 0u);
}

std::vector<svScope>& HandlesSeenInC() {
  static std::vector<svScope> handles;
  return handles;
}

int FetchThenStore() {
  svScope scope = svGetScope();
  HandlesSeenInC().push_back(scope);
  int found = FetchUnderTheSharedKey();
  if (svPutUserData(scope, &UserKeysAndData()[0], &UserKeysAndData()[1]) != 0) {
    return -2;
  }
  return found;
}

TEST(UserDataInADesign, InstancesShareNoDataAndHaveDistinctHandles) {
  SimFixture f;
  HandlesSeenInC().clear();
  RunDesignWithC(
      "module m;\n"
      "  import \"DPI-C\" context function int use_data();\n"
      "  int first, second;\n"
      "  initial begin\n"
      "    first = use_data();\n"
      "    #1 second = use_data();\n"
      "  end\n"
      "endmodule\n"
      "module apart;\n"
      "  m i1();\n"
      "  m i2();\n"
      "endmodule\n",
      f, {{"use_data", CAddress(&FetchThenStore)}}, "annex_h_09_03_apart");
  EXPECT_EQ(DesignValue(f, "i1.first"), 0u);
  EXPECT_EQ(DesignValue(f, "i2.first"), 0u);
  EXPECT_EQ(DesignValue(f, "i1.second"), 1u);
  EXPECT_EQ(DesignValue(f, "i2.second"), 1u);
  ASSERT_EQ(HandlesSeenInC().size(), 4u);
  EXPECT_NE(HandlesSeenInC()[0], HandlesSeenInC()[1]);
  EXPECT_EQ(HandlesSeenInC()[0], HandlesSeenInC()[2]);
}

int AskForTheCaller() {
  const char kUntouched = 0;
  const char* file = &kUntouched;
  int line = -7;
  const bool kAnswered = svGetCallerInfo(&file, &line) != 0;
  return kAnswered ? static_cast<int>(file != &kUntouched && line == 4)
                   : static_cast<int>(file == &kUntouched && line == -7);
}

TEST(CallerInfoInADesign, TheCallLineIsGivenOrTheOutputsAreLeftAlone) {
  SimFixture f;
  RunDesignWithC(
      "module t;\n"
      "  import \"DPI-C\" context function int ask();\n"
      "  int r;\n"
      "  initial r = ask();\n"
      "endmodule\n",
      f, {{"ask", CAddress(&AskForTheCaller)}}, "annex_h_09_03_caller");
  EXPECT_EQ(DesignValue(f, "r"), 1u);
}

}  // namespace
