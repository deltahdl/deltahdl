#include <gtest/gtest.h>

#include <string>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ChargeStrengthPosition,
     DISABLED_AChargeStrengthWhereADriveStrengthGoesIsReported) {
  for (const std::string& item :
       {"assign (large) y = a;", "assign (small) y = a;",
        "buf (medium) g(y, a);", "and (small) g(y, a, a);",
        "bufif1 (large) g(y, a, a);", "pullup (medium) p(y);",
        "if (1) begin : gb assign (large) y = a; end",
        "for (genvar i = 0; i < 1; i++) begin : lp buf (small) g(y, a); end"}) {
    std::string src = "module m;\n  wire y, a;\n  ";
    src += item;
    src += "\nendmodule\n";
    auto r = Parse(src);
    EXPECT_TRUE(ReportedError(r.diags, "charge strength", 3, "28.11")) << item;
  }
}

TEST(ChargeStrengthPosition, ADriveStrengthInThosePositionsIsAccepted) {
  for (const std::string& item :
       {"assign (strong0, weak1) y = a;", "assign (weak1, pull0) y = a;",
        "buf (pull0, pull1) g(y, a);", "and (supply0, highz1) g(y, a, a);",
        "bufif1 (weak0, strong1) g(y, a, a);", "pullup (strong1) p(y);",
        "if (1) begin : gb assign (pull0, pull1) y = a; end",
        ("for (genvar i = 0; i < 1; i++) begin : l buf (weak0, weak1) g(y, a); "
         "end")}) {
    std::string src = "module m;\n  wire y, a;\n  ";
    src += item;
    src += "\nendmodule\n";
    auto r = Parse(src);
    EXPECT_FALSE(r.has_errors) << item;
  }
}

}  // namespace
