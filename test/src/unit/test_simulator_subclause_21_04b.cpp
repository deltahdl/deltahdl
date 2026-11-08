#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

void LoadText(SimFixture& f, const std::string& tag, const std::string& task,
              const std::string& text) {
  std::string path = "/tmp/deltahdl_t2104b_" + tag + ".mem";
  {
    std::ofstream ofs(path);
    ofs << text;
  }
  RunCapture("module t;\n  reg [7:0] mem [0:15];\n  initial " + task + "(\"" +
                 path + "\", mem);\nendmodule\n",
             f);
  std::remove(path.c_str());
}

TEST(ReadmemFileContents, AtFollowedBySpaceIsReported) {
  SimFixture f;
  LoadText(f, "at_space", "$readmemh", "@ 10\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'@' is not followed directly by a hexadecimal "
                            "address",
                            3, "21.4"));
}

TEST(ReadmemFileContents, AtFollowedByNonHexDigitsIsReported) {
  for (const char* text : {"@zz\n", "@1g\n"}) {
    SimFixture f;
    LoadText(f, "at_nonhex", "$readmemh", text);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'@' is not followed directly by a hexadecimal "
                              "address",
                              3, "21.4"))
        << text;
  }
}

TEST(ReadmemFileContents, WellFormedAddressesAreAccepted) {
  SimFixture f;
  LoadText(f, "at_ok", "$readmemh", "@0a 11\n@0B 22\n");
  EXPECT_FALSE(f.has_errors);
}

TEST(ReadmemFileContents, SizedBasedNumberIsReported) {
  SimFixture f;
  LoadText(f, "sized", "$readmemh", "8'hff\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not an unsized hexadecimal number", 3, "21.4"));
}

TEST(ReadmemFileContents, NonHexDigitUnderReadmemhIsReported) {
  SimFixture f;
  LoadText(f, "nonhex", "$readmemh", "fg\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not an unsized hexadecimal number", 3, "21.4"));
}

TEST(ReadmemFileContents, NonBinaryDigitUnderReadmembIsReported) {
  SimFixture f;
  LoadText(f, "nonbin", "$readmemb", "102\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not an unsized binary number", 3, "21.4"));
}

TEST(ReadmemFileContents, NumbersOfTheRadixAreAccepted) {
  SimFixture f;
  LoadText(f, "ok_b", "$readmemb",
           "1010_0101 // a comment\nxxzz0011 /* another */ 1\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
