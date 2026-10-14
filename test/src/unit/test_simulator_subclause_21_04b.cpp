// §21.4 Loading memory array data from a file — what the load file may hold.
// The file holds only white space, comments, @-addresses and numbers; an
// address is an `@` followed directly by a hexadecimal number, and a number
// carries neither a length nor a base and is written in the radix the task
// name fixes. A token of any other form is reported rather than read.
#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Loads `text` through `task` into a 16-word memory, running in `f` so a test
// can read the diagnostics the load raised; the call stands on line 3.
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

// §21.4: no white space stands between the `@` and its number, so `@ 10` is
// not an address; it is reported rather than read as address 0 followed by
// the data word 10.
TEST(ReadmemFileContents, AtFollowedBySpaceIsReported) {
  SimFixture f;
  LoadText(f, "at_space", "$readmemh", "@ 10\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'@' is not followed directly by a hexadecimal "
                            "address",
                            3, "21.4"));
}

// §21.4: an address is a hexadecimal number, so `@zz` and `@1g` are not
// addresses.
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

// §21.4: a well-formed address in either case of digit is accepted.
TEST(ReadmemFileContents, WellFormedAddressesAreAccepted) {
  SimFixture f;
  LoadText(f, "at_ok", "$readmemh", "@0a 11\n@0B 22\n");
  EXPECT_FALSE(f.has_errors);
}

// §21.4: a number carries neither a length nor a base, so `8'hff` is reported
// rather than loaded as 8ff.
TEST(ReadmemFileContents, SizedBasedNumberIsReported) {
  SimFixture f;
  LoadText(f, "sized", "$readmemh", "8'hff\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not an unsized hexadecimal number", 3, "21.4"));
}

// §21.4: $readmemh reads hexadecimal numbers, so a `g` is no digit of one.
TEST(ReadmemFileContents, NonHexDigitUnderReadmemhIsReported) {
  SimFixture f;
  LoadText(f, "nonhex", "$readmemh", "fg\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not an unsized hexadecimal number", 3, "21.4"));
}

// §21.4: $readmemb reads binary numbers, so a `2` is no digit of one and is
// reported rather than read as the low bit of its value.
TEST(ReadmemFileContents, NonBinaryDigitUnderReadmembIsReported) {
  SimFixture f;
  LoadText(f, "nonbin", "$readmemb", "102\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not an unsized binary number", 3, "21.4"));
}

// §21.4: digits of the radix with x, z and underscores, separated by white
// space and comments, are what the file may hold, and draw no report.
TEST(ReadmemFileContents, NumbersOfTheRadixAreAccepted) {
  SimFixture f;
  LoadText(f, "ok_b", "$readmemb",
           "1010_0101 // a comment\nxxzz0011 /* another */ 1\n");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
