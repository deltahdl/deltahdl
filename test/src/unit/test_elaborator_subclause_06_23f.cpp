#include <gtest/gtest.h>

#include <format>
#include <string>
#include <string_view>

#include "helpers_declaration_places.h"

using namespace delta;

namespace {

constexpr std::string_view kParams =
    "  int nq [$];\n"
    "  int na [3];\n"
    "  localparam type(nq) PTQ = '{1, 2};\n"
    "  localparam type(na) PTA = '{1, 2, 3};\n"
    "  localparam int SQ [$] = '{1, 2};\n"
    "  localparam int SA [3] = '{1, 2, 3};\n"
    "  int x;\n";

constexpr std::string_view kReport =
    "'$' may stand only in a queue's dimension or select";

TEST(ParameterOfTypeReferenceElaborator, FixedSizeArrayRefusesDollarSelect) {
  for (std::string_view select : {"PTA[$]", "SA[$]"}) {
    const std::string kBody =
        std::format("{}  initial x = {};\n", kParams, select);
    ExpectReportedIn({"module", "interface", "program"}, kBody, kReport, select,
                     "6.20.7");
  }
}

TEST(ParameterOfTypeReferenceElaborator, QueueTakesDollarSelect) {
  const std::string kBody =
      std::format("{}{}", kParams,
                  "  initial x = PTQ[$] + PTQ.size() + PTA[2] + $size(PTA);\n"
                  "  initial x = SQ[$] + SQ.size() + SA[2] + $size(SA);\n");
  ExpectCleanIn({"module", "interface", "program", "generate block"}, kBody);
}

}  // namespace
