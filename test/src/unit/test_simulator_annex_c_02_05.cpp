#include <gtest/gtest.h>

#include <string>

#include "simulator/dpi_runtime.h"

namespace delta {
namespace {

// Annex C.2.5: Data read API.
//
// IEEE 1800-2009 removed the Data Read API that earlier appeared in Clause 30
// and Annex I of IEEE 1800-2005, and IEEE 1800-2023 still does not carry it.
// Unlike a routine that was renamed, the Data Read API has no replacement in
// this standard. The runtime keeps the interface operational for callers that
// predate the removal, but every public entry point now records a deprecation
// diagnostic announcing that the API no longer appears in the language - so a
// program reaching it is told the interface is gone and where it was last
// specified.

// A fresh handle has not reported anything: the deprecation is observed only
// once the API is actually exercised, so the diagnostic tracks real use.
TEST(DataReadApiDeprecated, IsSilentUntilTheApiIsUsed) {
  DataReadApi api;
  EXPECT_FALSE(api.DeprecationReported());
  EXPECT_EQ(api.DeprecationCount(), 0u);
  EXPECT_TRUE(api.LastDeprecation().empty());
}

// Reading through the API - the operation the "Data Read API" is named for -
// records the deprecation. The message names IEEE 1800-2005 as the last
// standard to specify the interface, telling the caller where the removed text
// can be found.
TEST(DataReadApiDeprecated, ReadingRecordsTheDeprecation) {
  DataReadApi api;

  api.GetValue("sig", DataReadFormat::kInt);

  EXPECT_TRUE(api.DeprecationReported());
  EXPECT_NE(api.LastDeprecation().find("deprecated"), std::string::npos);
  EXPECT_NE(api.LastDeprecation().find("1800-2005"), std::string::npos);
}

// No replacement is named. This is what distinguishes the Data Read API's full
// removal from a renamed routine: the diagnostic reports the interface as gone
// with nowhere in this standard to move to.
TEST(DataReadApiDeprecated, ReportsRemovalWithoutAReplacement) {
  DataReadApi api;

  api.GetValue("sig", DataReadFormat::kInt);

  EXPECT_NE(api.LastDeprecation().find("no replacement"), std::string::npos);
}

// The deprecation is unconditional across the API surface: writing, storing,
// and registering value-change callbacks each draw the same diagnostic, since
// the whole interface - not one routine within it - is the deprecated thing.
TEST(DataReadApiDeprecated, EveryPublicEntryPointReportsIt) {
  DataReadValue val;
  val.format = DataReadFormat::kInt;
  val.int_val = 7;

  {
    DataReadApi api;
    api.StoreVariable("a", val);
    EXPECT_TRUE(api.DeprecationReported());
  }
  {
    DataReadApi api;
    api.PutValue("a", val);
    EXPECT_TRUE(api.DeprecationReported());
  }
  {
    DataReadApi api;
    api.RegisterValueChangeCb(
        "a", [](std::string_view, const DataReadValue&) {});
    EXPECT_TRUE(api.DeprecationReported());
  }
}

// The diagnostic counts every use rather than latching once, so repeated reads
// keep announcing the deprecation. GetValue does not cascade into other entry
// points, so the count matches the number of calls exactly.
TEST(DataReadApiDeprecated, CountsEveryUse) {
  DataReadApi api;

  api.GetValue("x", DataReadFormat::kInt);
  api.GetValue("y", DataReadFormat::kInt);
  api.GetValue("z", DataReadFormat::kInt);

  EXPECT_EQ(api.DeprecationCount(), 3u);
}

// The deprecation is a side channel: it does not disturb the live data the API
// still serves. A stored value reads back unchanged even though the read and
// the store both recorded the deprecation - the interface remains usable while
// announcing that it is gone.
TEST(DataReadApiDeprecated, LiveBehaviorIsUnaffected) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kInt;
  val.int_val = 99;

  api.StoreVariable("v", val);
  auto result = api.GetValue("v", DataReadFormat::kInt);

  EXPECT_EQ(result.int_val, 99);
  EXPECT_TRUE(api.DeprecationReported());
}

// Edge case: a write fans out to registered value-change callbacks internally,
// but that internal dispatch is not itself a caller-facing use of the API. One
// PutValue is therefore counted once, not twice - the deprecation tracks the
// entry point the program reached, not the runtime's own bookkeeping.
TEST(DataReadApiDeprecated, WriteCountsOnceDespiteCallbackCascade) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kInt;
  val.int_val = 5;
  api.RegisterValueChangeCb("sig",
                            [](std::string_view, const DataReadValue&) {});
  ASSERT_EQ(api.DeprecationCount(), 1u);  // the registration itself

  api.PutValue("sig", val);

  EXPECT_EQ(api.DeprecationCount(), 2u);  // +1 for the write, not +2
}

// Edge case: the deprecation message is uniform across the API surface, not a
// property of the read path alone. A write reports the same removal - naming
// the last standard to specify the interface and that nothing replaces it - so
// every way into the deprecated API tells the caller the same thing.
TEST(DataReadApiDeprecated, WritePathCarriesTheSameDiagnostic) {
  DataReadApi api;
  DataReadValue val;
  val.format = DataReadFormat::kInt;
  val.int_val = 5;

  api.PutValue("sig", val);

  EXPECT_NE(api.LastDeprecation().find("1800-2005"), std::string::npos);
  EXPECT_NE(api.LastDeprecation().find("no replacement"), std::string::npos);
}

}  // namespace
}  // namespace delta
