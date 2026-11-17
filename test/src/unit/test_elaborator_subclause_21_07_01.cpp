#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string DumpTaskIn(const std::string& call) {
  return "module t;\n"
         "  logic [7:0] a, b; real r; string s;\n"
         "  initial " +
         call +
         ";\n"
         "endmodule\n";
}

void ExpectReported(const std::string& call, const std::string& message,
                    const char* subclause) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(DumpTaskIn(call), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 3, subclause))
      << call;
}

void ExpectAccepted(const std::string& call) {
  ElabFixture f;
  Elaborate(DumpTaskIn(call), f);
  EXPECT_FALSE(f.has_errors) << call;
}

TEST(DumpfileArgumentList, DISABLED_TwoFilenamesAreReported) {
  ExpectReported("$dumpfile(\"a.vcd\", \"b.vcd\")",
                 "$dumpfile takes at most one filename", "21.7.1.1");
}

TEST(DumpfileArgumentList, DISABLED_ARealFilenameIsReported) {
  ExpectReported("$dumpfile(r)",
                 "the filename of $dumpfile must be a string or an integral "
                 "value",
                 "21.7.1.1");
}

TEST(DumpfileArgumentList, EveryAllowedFormIsAccepted) {
  for (const char* call : {"$dumpfile", "$dumpfile()", "$dumpfile(\"d.vcd\")",
                           "$dumpfile(s)", "$dumpfile(a)"}) {
    ExpectAccepted(call);
  }
}

TEST(DumpvarsArgumentList, DISABLED_ALiteralScopeIsReported) {
  ExpectReported("$dumpvars(0, 5)",
                 "$dumpvars names only modules and variables after its level",
                 "21.7.1.2");
}

TEST(DumpvarsArgumentList, DISABLED_AnExpressionScopeIsReported) {
  ExpectReported("$dumpvars(0, a + b)",
                 "$dumpvars names only modules and variables after its level",
                 "21.7.1.2");
}

TEST(DumpvarsArgumentList, EveryAllowedFormIsAccepted) {
  for (const char* call : {"$dumpvars", "$dumpvars(1)", "$dumpvars(0, t)",
                           "$dumpvars(1, a, b)", "$dumpvars(0, t, t.a)"}) {
    ExpectAccepted(call);
  }
}

TEST(DumpOffOnArgumentList, DISABLED_AnArgumentIsReported) {
  for (const char* task : {"$dumpoff", "$dumpon"}) {
    for (const char* args : {"()", "(1)", "(a)", "(a, b)"}) {
      ExpectReported(std::string(task) + args,
                     std::string(task) + " takes no arguments", "21.7.1.3");
    }
  }
}

TEST(DumpOffOnArgumentList, TheBareFormIsAccepted) {
  ExpectAccepted("$dumpoff");
  ExpectAccepted("$dumpon");
}

void ExpectEveryArgumentListReported(const std::string& task,
                                     const char* subclause) {
  for (const char* args : {"()", "(1)", "(a, b)"}) {
    ExpectReported(task + args, task + " takes no arguments", subclause);
  }
}

TEST(DumpallAndDumpflushArgumentList, DISABLED_AnArgumentIsReported) {
  ExpectEveryArgumentListReported("$dumpall", "21.7.1.4");
  ExpectEveryArgumentListReported("$dumpflush", "21.7.1.6");
}

TEST(DumpallAndDumpflushArgumentList, TheBareFormIsAccepted) {
  ExpectAccepted("$dumpall");
  ExpectAccepted("$dumpflush");
}

TEST(DumplimitArgumentList, DISABLED_AMissingFilesizeIsReported) {
  for (const char* call : {"$dumplimit", "$dumplimit()"}) {
    ExpectReported(call, "$dumplimit takes one filesize", "21.7.1.5");
  }
}

TEST(DumplimitArgumentList, DISABLED_TwoArgumentsAreReported) {
  ExpectReported("$dumplimit(100, 200)", "$dumplimit takes one filesize",
                 "21.7.1.5");
}

TEST(DumplimitArgumentList, OneFilesizeIsAccepted) {
  for (const char* call :
       {"$dumplimit(100)", "$dumplimit(a)", "$dumplimit(a * 4)"}) {
    ExpectAccepted(call);
  }
}

}  // namespace
