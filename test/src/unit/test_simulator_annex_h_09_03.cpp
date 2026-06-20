#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

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
  const char* kName = "top.dut_h_09_03.u_alu";
  const DpiScope* registered = DpiRegisterScope(kName);
  ASSERT_NE(registered, nullptr);

  svScope handle = svGetScopeFromName(kName);
  EXPECT_EQ(handle, static_cast<svScope>(const_cast<DpiScope*>(registered)));
  ASSERT_NE(handle, nullptr);

  EXPECT_STREQ(svGetNameFromScope(handle), kName);

  // Registering the same name again is idempotent: the same recognized handle
  // comes back, so the name resolves deterministically.
  EXPECT_EQ(svGetScopeFromName(kName), handle);
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

}  // namespace
