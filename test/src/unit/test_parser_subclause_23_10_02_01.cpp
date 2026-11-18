#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OrderedParameterValueList, NoPositionMayBeLeftEmpty) {
  const char* const kLists[] = {"#(, 5)", "#(1, , 3)", "#(1, )"};
  for (const char* list : kLists) {
    SCOPED_TRACE(list);
    auto r =
        Parse(std::string("module top;\n  c ") + list + " u();\nendmodule\n");
    EXPECT_TRUE(ReportedError(
        r.diags,
        "an ordered parameter value list cannot leave a position empty", 2,
        "23.10.2.1"));
  }
}

TEST(OrderedParameterValueList, EveryPositionWrittenIsAccepted) {
  const char* const kLists[] = {"#(5)", "#(1, 2, 3)", "#(1, 2)"};
  for (const char* list : kLists) {
    SCOPED_TRACE(list);
    auto r =
        Parse(std::string("module top;\n  c ") + list + " u();\nendmodule\n");
    EXPECT_FALSE(r.has_errors);
  }
}

}  // namespace
